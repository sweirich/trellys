{-# LANGUAGE RankNTypes, TemplateHaskell, FlexibleContexts, FlexibleInstances,
TypeSynonymInstances, GADTs, ScopedTypeVariables, MultiParamTypeClasses,
UndecidableInstances, PackageImports #-}

module Language.SepPP.Match
 (PatMatch(..),Match,
 emptyMatch, singletonMatch, extendMatch, extendMatches, applyMatch, lookupMatch,
 isInstantiated) where


import Language.SepPP.Syntax
import Language.SepPP.TCUtils
import Language.SepPP.PrettyPrint


import Generics.RepLib
import qualified Generics.RepLib as RL
import Unbound.LocallyNameless hiding (Con,isTerm,Val,join,Refl,Equal)
import Text.Parsec.Pos


import Text.PrettyPrint
import qualified Data.Map as M
import "mtl" Control.Monad.Error
import Data.List(intersect)


-- * Pattern matching
class (Rep1 PatMatchD t, Rep t) => PatMatch t where
  -- The '[EName]' parameter is a list of the regular variables (Exprs built
  -- with the Var constructor) that should be treated as metavars for the
  -- purpose of matching.
  match :: (MonadError TypeError m, Monad m) => [EName] -> t -> t -> m Match
  match  = matchR1 rep1


data PatMatchD t = PatMatchD {  matchD :: forall m s. (Monad m, MonadError TypeError m) =>  [EName] -> t -> t -> m Match }
instance PatMatch t => Sat (PatMatchD t) where
  dict = PatMatchD match


instance PatMatch Expr where

  match vars (Pos _ t1) t2 = match vars t1 t2
  match vars t1 (Pos _ t2) = match vars t1 t2
  match vars t v@(Var _) = typeError "When matching, meta-variable cannot occur on RHS" []
  -- Note: The Var/Var case and Term/Var case should never happen, since we're doing matching and not unification.
  match vars (Var n) t
      | n `elem` vars = singletonMatch n t
      | Var n' <- t = do
         unless (n' == n) $ typeError "Cannot match dissimilar variables"
                                       [(text "First variable", disp n)
                                       ,(text "Second variable", disp n')]
         return emptyMatch
      | otherwise = typeError "Cannot match non-metavariable with a term"
                      [(text "The variable", disp n)
                      ,(text "The term", disp t)]



  match vars t u = matchR1 rep1 vars t u



matchR1 :: (MonadError TypeError m) => R1 PatMatchD t -> [EName] -> t -> t -> m Match
matchR1 Int1 _  x y  = unless (x == y) ( matchError x y) >> return emptyMatch
matchR1 Integer1 _ x y = unless (x == y) (matchError x y) >> return emptyMatch
matchR1 Char1 _  x y = unless (x == y) (matchError x y) >> return emptyMatch
matchR1 (Data1 _ cons) vars x y = loop cons x y where
   loop (RL.Con emb reps : rest) x y =
     case (from emb x, from emb y) of
      (Just p1, Just p2) -> match1 reps vars p1 p2
      (Nothing, Nothing) -> loop rest x y
      (_,_)              -> matchError x y
matchR1 _ _ _ _ = typeError "Could not match values." []

match1 ::  MonadError TypeError m => MTup PatMatchD l -> [EName] -> l -> l -> m Match
match1 MNil _ Nil Nil = return emptyMatch
match1 (r :+: rs) vars (p1 :*: t1) (p2 :*: t2) = do
  s1 <- matchD r vars p1 p2
  s2 <- match1 rs vars t1 t2
  extendMatches s1 s2



matchError t1 t2 = typeError "Could not match values." [] -- [(text "First value", disp t1), (text "Second value", disp t2)]
instance Disp Integer where
  disp = text . show

instance Disp Char where
  disp = char

instance PatMatch Int where
  match _ x y = do
    when (x /= y) $ fail "PatMatch failed on Int."
    return emptyMatch
instance PatMatch Char where
  match _ x y = do
    when (x /= y) $ fail "PatMatch failed on Char."
    return emptyMatch

instance (PatMatch p, PatMatch n) => PatMatch (Bind p n)
instance (PatMatch l, PatMatch r) => PatMatch (l,r)
instance (PatMatch x, PatMatch y, PatMatch z) => PatMatch (x,y,z)
instance (PatMatch w, PatMatch x, PatMatch y, PatMatch z) => PatMatch (w,x,y,z)
instance PatMatch Bool
instance PatMatch t => PatMatch (Embed t)
instance PatMatch SourcePos
instance PatMatch a => PatMatch [a]
instance PatMatch Stage
instance PatMatch Tele
instance PatMatch Kind
instance PatMatch Integer
instance PatMatch EName where
  match _ x y = do
    when (x /= y) (typeError "PatMatch Failed on names." [(text "First Name", disp x), (text "Second Name", disp y)])
    return emptyMatch

instance PatMatch a => PatMatch (Maybe a)
instance (PatMatch a, PatMatch  b) => PatMatch (Rebind a b)

-- No idea why this is required...
instance (PatMatch t) => PatMatch (R t)


newtype Match = Match (M.Map EName Expr) deriving Show


instance Alpha Match
instance Alpha (M.Map EName Expr)


emptyMatch = Match M.empty
singletonMatch n t = extendMatch n t emptyMatch
-- extendMatch :: EName -> Expr -> Match -> TCMonad Match
extendMatch n new (Match m)
  | Just old <- M.lookup n m = do
                 unless (new `aeq` old) $ typeError "Conflicting values for name"
                          [(text "The name", disp n)
                          ,(text "New value", disp new)
                          ,(text "Existing value", disp old)]
                 return  m'
  | otherwise = return m'
  where m' = Match $ M.insert n t' $ M.map (subst n t') m
        t' = substs (M.toList m) new

extendMatches (Match m0) m1 = foldM (\sub (n,t) -> extendMatch n t sub) m1 (M.toList m0)
applyMatch (Match m) t = substs (M.toList m) t

lookupMatch n (Match m) = M.lookup n m

-- Check to see if the input type contains any of the marked metavars in vars.
isInstantiated vars ty
  | null metavars = Just ty
  | otherwise = Nothing
  where allvars = fv ty
        metavars = allvars `intersect` vars


$(derive_abstract [''M.Map])
$(derive [''Match])

