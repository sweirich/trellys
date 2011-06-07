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




eval t = do

  -- dt <- disp t
  -- liftIO $ print $ text "Evaluating" <+> dt
  t' <- reduce t return
  -- dt' <- disp t'
  -- liftIO $ putStrLn "-----------------"
  -- liftIO $ print $ dt $$ text "-->" $$ dt'
  liftIO $ putStrLn "======================"
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
                             liftIO $ print $
                                    text "(Beta) Reduced" $$ dt $$ text "to" $$
                                    dt2'
                             reduce t2' k)
             k' t@(Rec binding) = do
                 dt <- disp t
                 ((f,(n,_)),body) <- unbind binding
                 reduce t2 (\v2 -> do
                              let t2' = substs [(f,t),(n,v2)] body
                              dt2' <- disp t2'
                              liftIO $ print $
                                text "(Rec) Reduced" $$ dt $$ text "to" $$
                                     dt2'
                              reduce t2' k)
             k' v1 = do
               dt <- disp v1
               liftIO $ print $ text "App stuck: " <+> dt
               liftIO $ print $ v1
               k (App v1 stage t2)
             k'' v = k' (down v)

   reduce' (Case scrutinee tp bindingAlts) k = do
     (_,alts') <- unbind bindingAlts
     reduce scrutinee (k'' alts')
    where k' alts t = do cs <- getCons t
                         (body :: Term) <- patMatch cs alts
                         dt <- disp (Case t tp bindingAlts)
                         dbody <- disp body
                         liftIO $ print $ text "(Case) Reduced"  $$
                                          dt $$
                                          text "to" $$
                                          dbody
                         reduce body k

          k'' alts t = k' alts (down t)

   reduce' v@(Lambda _ _ _) k =  k v
   reduce' v@(Rec _) k = k v
   reduce' v@(Var _) k = k v
   reduce' c@(Con _) k = k c
   reduce' (Pos _ t) k = reduce' t k
   reduce' (Parens t) k = reduce' t k


   reduce' t k = do
    die (t <++> "can't be evaluated.")



patMatch (c,args) [] = fail "No Pattern Match"
patMatch t@(Con c,args) (b:bs) = do
  ((cname,vars),body) <- unbind b
  if string2Name cname == c
     then return $ substs (zip vars args) body
     else patMatch t bs


getCons :: Term -> TCMonad (Term,[Term])
getCons t@(Con _) = return (t,[])
getCons t = case splitApp t of
              (c@(Con _):cs) -> return (c,cs)
              _ -> throwError $
                   strMsg $ "Case argument doesn't reduce to a construction"
