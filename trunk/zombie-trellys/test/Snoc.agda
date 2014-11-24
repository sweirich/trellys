-- A challenge for Agda pattern matching 
-- from Eric Mertens
-- https://plus.google.com/105882209409368927186/posts/eHEV4tRLhiC
----- actually public. The share of it I found first was private. 

-- Eric writes: 
--    Ulf Norell went so far as to say “it’s quite fun”.  
--    This problem is just a little trickier than it looks and might even teach you something about using “with”!

-- found with google "agda tricky pattern matching"  

module Snoc (A : Set) where

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

infixr 5 _∷_ _++_

data List : Set where
  _∷_ : A → List → List
  []  : List

_++_ : List → List → List
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

snoc : List → A → List
snoc xs x = xs ++ x ∷ []

-- this helper would make it SOOO much easier. But nope, not allowed.
-- EDIT: maybe it wouldn't help that much.
{-
::inv2 : ∀ {x y : A}{xs ys : List} -> (x ∷ xs) ≡ (y ∷ ys) -> xs ≡ ys 
::inv2 refl = refl
-}

-- Your challenge is to implement the following using only pattern matching
-- and with clauses.
snoc-inv : ∀ xs ys z → (snoc xs z ≡ snoc ys z) → xs ≡ ys
snoc-inv (x ∷ xs') (y ∷ ys') z pf 
  with (snoc xs' z) | (snoc ys' z) 
    | inspect (snoc xs') z | inspect (snoc ys') z
snoc-inv (.y ∷ xs') (y ∷ ys') z refl 
  | .s2 | s2 | [ p ] | [ q ] with (snoc-inv xs' ys' z (trans p (sym q))) 
snoc-inv (.y ∷ .ys') (y ∷ ys') z refl 
  | .s2 | s2 | [ p ] | [ q ] | refl = refl
snoc-inv (x ∷ x₁ ∷ xs) [] z () 
snoc-inv (x ∷ []) [] z ()
snoc-inv [] (x ∷ x₁ ∷ ys) z () 
snoc-inv [] (x ∷ []) z ()
snoc-inv [] [] z refl = refl
