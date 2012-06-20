{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, GADTs, TypeOperators, TypeFamilies, RankNTypes, PackageImports #-}
module Language.SepPP.Eval where

import Language.SepPP.Syntax(EExpr(..),noTCast,unrollApp)
import Language.SepPP.PrettyPrint
import Language.SepPP.TCUtils
import Language.SepPP.Options

import Generics.RepLib hiding (Con(..))
import Unbound.LocallyNameless hiding (Con(..),Equal,Refl)
-- import Control.Monad((>=>))
import "mtl" Control.Monad.Trans
import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.Error
import Text.PrettyPrint(render, text,(<+>),($$))

-- compile-time configuration: should reduction steps be logged
debugReductions = False

eval steps t = do
  t' <- erase t
  -- emit $ "Reducing" <++> t'
  evalErased steps t'

evalErased steps t = reduce steps t (\_ tm -> return tm)

logReduce t t' = do
  lr <- getOptShowReductions
  when lr $ do
    emit $ ("reduced" $$$ t $$$ "to" $$$ t')
    emit $  "===" <++> "==="

reduce,reduce' :: Integer -> EExpr -> (Integer -> EExpr -> TCMonad EExpr) -> TCMonad EExpr
reduce steps e k = do
  rewrite <- lookupRewrite e
  case rewrite of
    Just rhs -> do
      -- emit $ "Rewrote" <++> e <++> "to" <++> rhs
      reduce steps rhs k
    Nothing -> reduce' steps e k



reduce' 0 t k = k 0 t
reduce' steps EAbort _ = return EAbort
reduce' steps v@(EVar n) k = do
     d <- lookupDef (translate n)
     case d of
       Just def -> do
         -- emit $ "Found a definition for" <++> v
         t' <- erase def
         logReduce v t'
         reduce (steps - 1) t' k
       Nothing -> do
         -- emit ("Can't reduce variable" <++> v)
         k steps v
reduce' steps t@(ECon _) k = k steps t



reduce' steps tm@(EApp t1 t2) k = do
   -- emit $ "Reducing app" <++> tm
   reduce steps t1 k'
  where k' 0 t1' = k 0 (EApp t1' t2)
        k' steps t1'@(ELambda binding) = do
          (x,body) <- unbind binding
          tp <- lookupTermProof t2
          case tp of
            Nothing -> do
              -- emit $  "No term proof for" <++> t2
              reduce steps t2 (\steps' v -> do
                              case v of
                                EAbort -> return EAbort
                                _ -> do
                                  val <- isValue v
                                  if steps' == 0 || not val
                                   then do
                                    -- emit $ "Stuck term" $$$ EApp t1' v
                                    k steps (EApp t1' v)
                                   else do
                                    let tm' = subst x v body
                                    logReduce (EApp t1' v) tm'
                                    reduce (steps - 1) tm' k)
            Just pf -> do
              -- emit $ "Inserting tcast for argument" <++> t2
              let tm' = subst x (ETCast t2) body
              reduce (steps - 1) tm' k

        k' steps t1'@(ERec binding) = do
          typeError "When evaluating, the term being applied is a 'Rec'. This should not happen."
                    [(text "The term being applied", disp t1'),
                     (text "The application", disp tm)]

        -- This *HAS* to be a bug:
        k' steps (ETCast e) = k' (steps-1) (ETCast e)
        k' steps v1 = do
          ev <- erasedSynValue v1

          if isCon v1 && ev
            then do
               -- emit $ "Looking for term proof for con argument. " <++> t2
               tp <- lookupTermProof t2
               case tp of
                 Nothing ->
                   reduce steps t2
                    (\steps' v2 -> do
                       tp <- lookupTermProof v2
                       let v2' = maybe v2 (\_ -> ETCast v2) tp
                       k steps (EApp v1 v2'))
                 Just pf -> do
                   -- emit $ "Got it" <++> t2
                   k steps (EApp v1 (ETCast t2))
             else k steps (EApp v1 t2)

        isCon (ECon _) = True
        isCon (EApp l _) = isCon l
        isCon _ = False


        isValue t = do
          tp <- lookupTermProof t
          disableValueRestriction <- getOptDisableValueRestriction
          ev <- erasedSynValue t
          case tp of
            Nothing -> return (ev || disableValueRestriction)
            Just _ -> return True


reduce' steps tm@(ECase scrutinee alts) k = do
  -- emit $ "Case scrutinee:" <++> scrutinee
  rw <- lookupRewrite scrutinee'
  case rw of
    Just rhs -> do
      -- emit $ "Got rewrite" <++> scrutinee' <++> "to" <++> rhs
      reduce steps (ECase rhs alts) k
    Nothing -> do
      -- emit $ "Can't find rewrite for" <++> (show scrutinee')
      -- showRewrites
      reduce steps scrutinee k'

  where k' 0 t = k 0 (ECase t alts)
        k' steps v =
          case unrollApp (unTCast v) of
            (ECon c,args) -> do
              branch <- substPat c args alts
              logReduce (ECase v alts) branch
              reduce (steps - 1) branch k
            _ -> do
              rw <- lookupRewrite (unTCast scrutinee)
              case rw of
                Just rhs -> do
                  reduce steps rhs k'
                Nothing -> do
                  -- emit $ "Stuck reduction"
                  -- showRewrites
                  k steps (ECase v alts)
        substPat c args [] = err $ "Can't find pattern for constructor"  ++ show c
        substPat c args (alt:alts) = do
          ((c',vs),body) <- unbind alt
          if string2Name c' == c
            then do
              -- We don't have pattern variables for type parameters
              -- (as opposed to data constructor parameters), so we
              -- have to drop any runtime type parameters.
              let args' = drop (length args - length vs) args
              return $ substs (zip vs args') body
             else substPat c args alts
        unTCast (ETCast t) = unTCast t
        unTCast t = t
        scrutinee' = noTCast scrutinee


reduce' steps (ELet binding) k = do
  ((x,Embed t), body) <- unbind binding
  let k' steps t' = do
          ev <- erasedSynValue t'
          if ev
             then do let body' = subst x t' body
                     reduce (steps - 1) body' k
             else return $ ELet (bind (x,Embed t') body)
  reduce steps t k'


reduce' steps t@(ERec binding) k = do
  ((f,args),body) <- unbind binding
  let t' = foldr (\n bdy -> ELambda (bind n bdy)) (subst f t body)  args
  k steps t'
reduce' steps t@(EPi s binding) k = do
  ((x,Embed tp),body) <- unbind binding
  let k' steps tp' =
        let k'' steps body' = k steps $ EPi s (bind (x,Embed tp') body') in
            reduce steps body k''
  reduce steps tp k'
reduce' steps t@(ELambda _) k = k steps t
reduce' steps EType k = k steps EType
reduce' steps (ETCast t) k = reduce steps t (\steps' val -> k steps' (ETCast val))

patMatch (c,args) [] = err "No Pattern Match"
patMatch t@(ECon c,args) (b:bs) = do
  ((cname,vars),body) <- unbind b
  if string2Name cname == c
     then return $ substs (zip vars args) body
     else patMatch t bs


-- getCons :: Expr -> Maybe (Expr,[Expr])
-- getCons t@(Con _) = return (t,[])
-- getCons t = case splitApp t of
--               (c@(Con _):cs) -> return (c,cs)
--               _ -> Nothing
