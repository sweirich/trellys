{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, GADTs, TypeOperators, TypeFamilies, RankNTypes #-}
module Language.SepPP.Eval where

import Language.SepPP.Syntax
import Language.SepPP.Zipper
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

  dt <- disp t
  -- liftIO $ print $ text "Evaluating" <+> dt
  t' <- reduce t return
  dt' <- disp t'
  liftIO $ print $ dt $$ text "-->" $$ dt'
  liftIO $ putStrLn "-----------------"
  -- die (t <++> "can't be evaluated.")
  return t'

reduce (App (Lambda _ _ binding) _ t2) k = do
  ((n,_),body) <- unbind binding
  reduce t2 (\v2 -> k (subst n v2 body))

reduce (App t1 stage t2) k =
    reduce t1 k'
  where k' (Lambda _ _ binding) = do
          ((n,_),body) <- unbind binding
          reduce t2 (\v2 -> k (subst n v2 body))
        k' t@(Rec binding) = do
          ((f,(n,_)),body) <- unbind binding
          reduce t2 (\v2 -> k (substs [(f,t),(n,v2)] body))
        k' v1 = do
          dt <- disp v1
          liftIO $ print $ text "App stuck: " <+> dt
          liftIO $ print $ v1
          k (App v1 stage t2)

reduce (Case scrutinee _ alts) k = reduce scrutinee k'
  where k' v = findAlt v
        findAlt v = die ("Looking for alt with " <++> v)

reduce v@(Rec _) k = k v
reduce v@(Var _) k = k v
reduce c@(Con _) k = k c
reduce (Pos _ t) k = reduce t k
reduce (Parens t) k = reduce t k

reduce t k = do
  die (t <++> "can't be evaluated.")


{-
eval t = reduction $ Just $ ZTop t

class Reducible t where

  type RMonad t :: (* -> *)
  -- | Perform a reduction. Return Nothing if this is not a redex.
  reduce :: t -> Maybe (RMonad t t)
  -- | Decompose a term; return the series of movements to get to the subterm of
  -- focus.
  decomp :: t -> Zipper t -> Maybe (Zipper t)

  -- | Deterimine if a form is a value.
  isValue :: t -> Bool


instance Reducible Term where
  type RMonad Term = TCMonad
  reduce (Pos _ t) = Nothing
  reduce t = Nothing
  decomp (Pos _ t) = down
  decomp t = error $ "Can't decompose " ++ show t


  isValue (Var x) = True
  isValue (Con x) = True
  isValue (Lambda _ _ _) = True
  isValue _ = False



-- reduction :: Maybe (Zipper Term) -> Mon Term
reduction Nothing = fail "No context"
reduction (Just context)
  | ZTop t <- context, isValue t = return t
  | otherwise =
    case get context of
      Nothing -> fail "No term in the context."
      Just t -> do
        case reduce t of
          Just m -> do
                  t' <- m
                  liftIO $ putStrLn (show t ++ "  -->   " ++ show t')
                  reduction (put t' context)
          Nothing -> case down context >>= decomp t of
                       Just c' -> reduction (Just c')
                       Nothing
                         | isValue t -> reduction (up context)
                         | otherwise -> do
                            liftIO $ putStrLn "Plugging in a non-value. This might not work out at all."
                            liftIO $ print t
                            reduction (up context)



reduce t@(App t1 stage t2) =
  case (t1,t2) of
    (Lambda _ _ binding, _)
      | isValue t2 -> do
         ((n,ty),body) <- unbind binding
         let t' = subst n t2 body
         dt <- disp t
         dt' <- disp t'
         liftIO $ putStrLn $ render $ dt <+> text "-->" <+> dt'
         reduce t'

      | otherwise -> do
          t2' <- reduce t2
          case t2' of
            Just t2'' -> reduce (App t1 stage t2)
            Nothing -> return (Just t)

    (Rec binding, t2)
      | isValue t2 -> do
                 ((f,(n,_)),body) <- unbind binding
                 reduce (subst f t1 $ subst n t2 body)
      | otherwise -> do
          t2' <- reduce t2
          case t2' of
            Just t2'' -> reduce (App t1 stage t2)
            Nothing -> return Nothing


    _ -> do
      t1' <- reduce t1
      case t1' of
            Just t'' -> reduce (App t1 stage t2)
            Nothing -> return Nothing

reduce (ConvCtx t ctx) = reduce t
reduce (Pos _ t) = reduce t
reduce (Parens t) = reduce t

reduce v@(Var _) = return $ Nothing
reduce v@(Con _) = return $ Nothing


reduce t = do
  dt <- disp t
  throwError $ strMsg  $ "Can't reduce " ++ show t -- render dt

isValue (Lambda _ _ _)  = True
isValue (Con _) = True
isValue (Var _) = True
isValue (Parens t) = isValue t
isValue (Pos _ t) = isValue t

-}