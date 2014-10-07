-- A challenge for Agda pattern matching 
-- from Eric Mertens
-- https://plus.google.com/105882209409368927186/posts/eHEV4tRLhiC

-- Eric writes: 
--    Ulf Norell went so far as to say "it's quite fun".  
--    This problem is just a little trickier than it looks and might even 
--    teach you something about using "with" !

module SnocEx (A : Set) where

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

cons-inj1 : ∀ {x xs y ys} -> ((x ∷ xs) ≡ y ∷ ys) -> x ≡ y
cons-inj1 refl = refl

cons-inj2 : ∀ {x xs y ys} -> x ∷ xs ≡ y ∷ ys -> xs ≡ ys
cons-inj2 refl = refl 

app-cons : ∀ {x xs y ys} -> x ≡ y -> xs ≡ ys -> x ∷ xs ≡ y ∷ ys
app-cons refl refl = refl 


-- Your challenge is to implement the following using only pattern matching
-- and with clauses.

-- Dan Licata's 2nd solution: directly copying the ZT version
-- using injectivity and congruence.
snoc-inv : ∀ xs ys z → (snoc xs z ≡ snoc ys z) → xs ≡ ys
snoc-inv (x ∷ xs') (y ∷ ys') z pf = 
   app-cons (cons-inj1 pf) (snoc-inv xs' ys' z (cons-inj2 pf))


snoc-inv [] [] z refl = refl
snoc-inv (x ∷ x₁ ∷ xs) [] z () 
snoc-inv (x ∷ []) [] z ()
snoc-inv [] (x ∷ x₁ ∷ ys) z () 
snoc-inv [] (x ∷ []) z ()
