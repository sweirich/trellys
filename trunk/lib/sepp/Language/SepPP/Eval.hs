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

eval t = do
  -- dt <- disp t
  -- liftIO $ print $ text "Evaluating" <+> dt
  when debugReductions $ liftIO $ putStrLn "======================"
  when debugReductions $ liftIO $ putStrLn "Evaluating"
  when debugReductions $ doDisp t >>= (liftIO . print)
  when debugReductions $ liftIO $ putStrLn "======================"
  t' <- reduce t return
  -- dt' <- disp t'
  -- liftIO $ putStrLn "-----------------"
  -- liftIO $ print $ dt $$ text "-->" $$ dt'
  -- liftIO $ putStrLn "======================"
  -- die (t <++> "can't be evaluated.")
  return t'


reduce t k = do
  dt <- disp t
  reduce' (down t) k where
   reduce' (App t1 stage t2) k = reduce' t1 k''
       where k' t@(Lambda _ _ binding) = do
                ((n,_),body) <- unbind binding
                reduce t2 (\v2 -> do
                             dt <- disp (App t stage v2)
                             let t2' = (subst n v2 body)
                             dt2' <- disp t2'
                             when debugReductions $ liftIO $ print $
                                    text "(Beta) Reduced" $$ dt $$ text "to" $$
                                    dt2'
                             reduce t2' k)
             k' t@(Rec binding) = do

                 ((f,(n,_)),body) <- unbind binding
                 reduce t2 (\v2 -> do
                              let t2' = substs [(f,t),(n,v2)] body
                              dt <- disp (App t stage v2)
                              dt2' <- disp t2'
                              when debugReductions $ liftIO $ print $
                                text "(Rec) Reduced" $$ dt $$ text "to" $$
                                     dt2'
                              reduce t2' k)
             k' v1 = do
               dt <- disp v1
               when debugReductions $ liftIO $ print $ text "App stuck: " <+> dt
               when debugReductions $ liftIO $ print $ v1
               k (App v1 stage t2)
             k'' v = k' (down v)

   reduce' (Case scrutinee tp bindingAlts) k = do
     (_,alts') <- unbind bindingAlts
     reduce scrutinee (k'' alts')
    where k' alts t
            | Just cs <- getCons t = do
                           (body :: Term) <- patMatch cs alts
                           dt <- disp (Case t tp bindingAlts)
                           dbody <- disp body
                           when debugReductions $ liftIO $ print $ text "(Case) Reduced"  $$
                                               dt $$
                                               text "to" $$
                                               dbody
                           reduce body k
            | otherwise = k (Case t tp bindingAlts)
          k'' alts t = k' alts (down t)


   reduce' (Let binding) k = do
      ((x,y,Embed t),body) <- unbind binding

      let k' v' = do
               sv <- synValue v'
               if sv
                 then reduce (subst x v' body) k
                 else k $ Let (bind (x,y,Embed v') body)
      reduce t k'



   reduce' v@(Lambda _ _ _) k =  k v
   reduce' v@(Rec _) k = k v
   reduce' v@(Var n) k =  do
     d <- lookupDef n
     case d of
       Just def -> do
               when debugReductions $  ((liftIO . print) =<<
                      ("(Def) Reduced"  $$$
                      v $$$
                      "to" $$$
                      def))

               reduce' def k
       Nothing -> do
               when debugReductions $ liftIO . print =<<
                     ("Can't reduce variable" <++> v)
               k v
   reduce' c@(Con _) k = k c
   reduce' (Pos _ t) k = reduce' t k


   reduce' t k = do
    die (t <++> "can't be evaluated.")



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





