-- A challenge for Agda pattern matching 
-- from Daniel Peebles
-- https://plus.google.com/106318233255980016498/posts/9MsYQAGEKSp

-- He writes: 
--    Ulf Norell went so far as to say “it’s quite fun”.  
--    This problem is just a little trickier than it looks and might even teach you something about using “with”!  

module Snoc (A : Set) where

infixr 5 _∷_ _++_
infixl 5 _|>_
infix 4 _≡_

data List : Set where
  _∷_ : A → List → List
  []  : List

_++_ : List → List → List
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_|>_ : List → A → List
xs |> x = xs ++ x ∷ []

data _≡_ (x : List) : List → Set where
  refl : x ≡ x

-- this helper would make it SOOO much easier. But nope, not allowed 
-- according to the challenge
::inv2 : ∀ {x y : A}{xs ys : List} -> (x ∷ xs) ≡ (y ∷ ys) -> xs ≡ ys 
::inv2 refl = refl

-- Your challenge is to implement the following using only pattern matching
-- and with clauses.
snoc-inv : ∀ xs ys z → xs |> z ≡ ys |> z → xs ≡ ys
snoc-inv (x ∷ xs) (y ∷ ys) z pf with (xs |> z)
...                                | sxs with (ys |> z) 
snoc-inv (.y ∷ xs) (y ∷ ys) z refl | .sys | sys with (snoc-inv xs ys z {! !} ) 
... | pf' = {! !}
snoc-inv (x ∷ x₁ ∷ xs) [] z () 
snoc-inv (x ∷ []) [] z ()
snoc-inv [] (x ∷ x₁ ∷ ys) z () 
snoc-inv [] (x ∷ []) z ()
snoc-inv [] [] z refl = refl