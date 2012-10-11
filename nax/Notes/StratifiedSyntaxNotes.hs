{-# LANGUAGE GADTs #-}

module Stratify where

{- -------------------------------------------------
The key ideas are

1) There is a single flat suntax that all terms, types, kinds, etc
belong to

2) That users declare the intent of every declaration.

3) That there is a subset of terms that is appropriate for
every intent. Some terms might be appropriate if their
intewnt is a type, but not if their intent was a term.

There are 4 intents

expressions (terms), types, kinds, large-eliminations

Let v be a countable set of variables



The flat syntax

e,t,k,l,x ::=  
  ::= v             -- variables
  |   1             -- the unit type
  |   *             -- Star the base kind
  |   #             -- Box the only Sort
  |  (v:t) -> t    (when v not in FV(t) we can write:  t->t )
  |  (v:k) => k
  |  (v:t) => k
  |  all (v:k) . t
  |  all (v:#) . k
  |  x x                  -- Application
  |  T x                  -- Construction
  |  case x of T x -> e   -- Deconstruction

----------------------------------------------- -}

-- Intent as uninhabited types

data Term
data Type
data Kind
data LE
data Sort

-- Singleton Intent

data Intent i where
 Term:: Intent Term
 Type:: Intent Type
 Kind:: Intent Kind
 LE:: Intent LE

-- Legal Abstractions
data Abstract i j where
  Fun:: Abstract Type Type  
  KK:: Abstract Kind Kind  
  KT:: Abstract Type Kind  
  PolyT:: Abstract Kind Type  
  PolyK:: Abstract Sort Kind  
  ELE:: Abstract Type LE  
  TLE:: Abstract Kind LE  

data Construction i where
  TCon:: Construction Type
  VCon:: Construction Term


 
data Syntax i where
  Var :: Intent i -> String -> Syntax i
  One :: Syntax Type
  Unit :: Syntax Term
  Star :: Syntax Kind
  Pi:: Abstract x y -> String -> Syntax y
  Con:: Construction i -> String -> [Syntax i] -> Syntax i
  App:: Syntax i -> Syntax i -> Syntax i
  Prod:: Syntax Type -> Syntax Type -> Syntax Type
  Pair:: Syntax Term -> Syntax Term -> Syntax Term
  
  
