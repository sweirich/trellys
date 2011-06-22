{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, GADTs, TypeOperators, TypeFamilies, RankNTypes #-}
module Language.SepPP.Eval where

import Language.SepPP.Syntax
import Language.SepPP.PrettyPrint
import Language.SepPP.TCUtils

import Generics.RepLib hiding (Con(..))
import Unbound.LocallyNameless hiding (Con(..))
-- import Control.Monad((>=>))
import Control.Monad.Trans
import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Text.PrettyPrint(render, text,(<+>),($$))

-- compile-time configuration: should reduction steps be logged
debugReductions = False



eval steps t = do
  -- dt <- disp t
  -- liftIO $ print $ text "Evaluating" <+> dt
  t' <- erase t
  evalErased steps t'

evalErased steps t = reduce steps t (\_ tm -> return tm)

logReduce _ _ = return ()
logReduce t t' = do
  emit $ ("reduced" $$$ t $$$ "to" $$$ t')
  emit $  "===" <++> "==="

reduce 0 t k = k 0 t

reduce steps v@(EVar n) k = do
     d <- lookupDef (translate n)
     case d of
       Just def -> do
              t' <- erase def
              logReduce v t'
              reduce (steps - 1) t' k
       Nothing -> do
               when debugReductions $ liftIO . print =<<
                     ("Can't reduce variable" <++> v)
               k steps v
reduce steps t@(ECon _) k = k steps t

reduce steps (EApp t1 t2) k = reduce steps t1 k'
  where k' 0 t1' = k 0 (EApp t1' t2)
        k' steps t1'@(ELambda binding) = do
          (x,body) <- unbind binding
          reduce steps t2 (\steps' v -> do
                       if steps' == 0
                          then return $ EApp t1' v
                          else do
                            let tm' = subst x v body
                            logReduce (EApp t1' v) tm'
                            reduce (steps - 1) tm' k)

        k' steps t1'@(ERec binding) = do

          reduce steps t2 (\steps' v -> do
                       if steps' == 0
                          then return $ EApp t1' v
                          else do
                                  ((f,x),body) <- unbind binding
                                  let tm' = (substs [(f,t1'),(x,v)] body)
                                  logReduce (EApp t1' v) tm'
                                  reduce (steps - 1) tm' k)
        k' steps t1 = k steps (EApp t1 t2)

reduce steps (ECase scrutinee alts) k = reduce steps scrutinee k'
  where k' 0 t = k 0 (ECase t alts)
        k' steps v = case findCon v [] of
                       (ECon c:args) -> do
                         branch <- substPat c args alts
                         reduce (steps - 1) branch k
                       _ -> do
                         rw <- lookupRewrite scrutinee
                         case rw of
                           Just rhs -> do
                                   emit $ "Found rewrite" <++> rhs
                                   reduce steps rhs k'
                           Nothing -> do
                             emit $  "No match" <++> v
                             k steps (ECase v alts)

        findCon :: ETerm -> [ETerm] -> [ETerm]
        findCon c@(ECon _) args = (c:args)
        findCon (EApp t a) args = findCon t (a:args)
        findCon _ _ = []
        substPat c args [] = err $ "Can't find constructor"
        substPat c args (alt:alts) = do
          ((c',vs),body) <- unbind alt
          if string2Name c' == c
             then return $ substs (zip vs args) body
             else substPat c args alts




reduce steps t@(ERec binding) k = k steps t
reduce steps t@(ELambda _) k = k steps t




reduce steps t k = die $ "reduce" <++> t

patMatch (c,args) [] = fail "No Pattern Match"
patMatch t@(Con c,args) (b:bs) = do
  ((cname,vars),body) <- unbind b
  if string2Name cname == c
     then return $ substs (zip vars args) body
     else patMatch t bs


getCons :: Term -> Maybe (Term,[Term])
getCons t@(Con _) = return (t,[])
getCons t = case splitApp t of
              (c@(Con _):cs) -> return (c,cs)
              _ -> Nothing



