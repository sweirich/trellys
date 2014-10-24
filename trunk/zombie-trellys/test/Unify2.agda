module Unify2 where

{- Agda version of unification example from POPL 2015 paper. 

This file actually defines unification several times. The first definition
uses a function for the occurs check, the second uses a more relational
version. The function described in the paper is at the end of the file.

-}

open import Function using (_∘_)
open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

open ≡-Reasoning

≡-cong : {A B : Set}{x y : A} -> (f : A -> B) -> (x ≡ y) -> f x ≡ f y
≡-cong f refl = refl


-- Common definitions to both versions 

data Term : Set where
  leaf   : Term
  branch : Term → Term → Term
  var    : ℕ → Term


-- Substitutions 

Substitution : Set 
Substitution = ℕ → Maybe Term

empty : Substitution 
empty x = nothing

singleton : (x : ℕ) → (t : Term) → Substitution
singleton x t y with  (x ≟ y)
...               | yes p = just t
...               | no ¬p = nothing

-- apply a substitution to a term
ap : Substitution → Term  → Term
ap s leaf = leaf
ap s (branch t1 t2) = branch (ap s t1) (ap s t2)
ap s (var x) with s x
...         | (just t) =  t
...         | (nothing) = var x

-- Composing substitutions
compose : Substitution → Substitution → Substitution
compose s1 s2 x with s2 x
...           | just t = just (ap s1 t)
...           | nothing = s1 x


-- reasoning about substitutions

apCompose : ∀ {s s'} → (t : Term) → ap (compose s s') t  ≡ ap s (ap s' t)
apCompose leaf = refl
apCompose (branch t1 t2) = cong₂ branch (apCompose t1) (apCompose t2)
apCompose {s} {s'} (var x) with s' x 
...               | just t' = refl
...               | nothing = refl

varSingleton : ∀ x t → t ≡ ap (singleton x t) (var x)
varSingleton x t with x ≟ x 
varSingleton x t | yes p =  refl
varSingleton x t | no ¬p = ⊥-elim (¬p refl)

-- result of unification
data Unify : (t1 t2 : Term) → Set where
  nomatch  : ∀{t1 t2} → Unify t1 t2
  match : ∀{t1 t2} (s : Substitution) → ap s t1 ≡ ap s t2 → Unify t1 t2   

-----------------------------------------------
-- version one, occurs check as a function 

-- returns true when x is not free in t
_∉FV_ : ℕ → Term → Bool
x ∉FV leaf = false
x ∉FV (branch t1 t2) = (x ∉FV t1) ∧ (x ∉FV t2)
x ∉FV (var y) with (x ≟ y)
...             | yes _ = false
...             | no _  = true

xisy : ∀ {x y} -> (x ∉FV (var y)) ≡ false -> x ≡ y 
xisy {x}{y} q with (x ≟ y) 
...  | (yes p) = p
...  | (no ¬p) with q 
...               | ()


-- interaction between singleton and ∉FV
singleton-∉FV : ∀ t x s → (x ∉FV t) ≡ true → ap (singleton x s) t ≡ t
singleton-∉FV leaf x s = λ _ →  refl
singleton-∉FV (branch t1 t2) x s with (x ∉FV t1) | inspect (_∉FV_ x) t1 | (x ∉FV t2) | inspect (_∉FV_ x) t2
...                                | false | [ p1 ] | _ | [ p2 ]  = λ()
...                                | true | [ p1 ] | false | [ p2 ] = λ()
...                                | true | [ p1 ] | true | [ p2 ]  = λ _ → cong₂ branch (singleton-∉FV t1 x s p1) 
                                                                                         (singleton-∉FV t2 x s p2) 
singleton-∉FV (var y) x s with (x ≟ y) 
...  | (yes p)  = λ ()
...  | (no ¬p)   = λ _ → refl




{-# NO_TERMINATION_CHECK #-}
unify : (t1 t2 : Term) → Unify t1 t2
unify leaf leaf = match empty refl
unify leaf (branch t2 t3) = nomatch
unify (branch t1 t2) leaf = nomatch
unify (branch t11 t12) (branch t21 t22) 
      with unify t11 t21 
...    | nomatch = nomatch
...    | match s p with unify (ap s t12) (ap s t22) 
...               | nomatch = nomatch
...               | match s' q 
  =  match (compose s' s) 
         (begin
            ap (compose s' s) (branch t11 t12)
          ≡⟨ apCompose (branch t11 t12)  ⟩
            ap s' (ap s (branch t11 t12))
          ≡⟨ refl ⟩
            branch (ap s' (ap s t11)) (ap s' (ap s t12))
          ≡⟨ cong₂ (λ t1 t2 → branch (ap s' t1) t2) p q ⟩
            branch (ap s' (ap s t21)) (ap s' (ap s t22))
          ≡⟨ refl ⟩
            ap s' (ap s (branch t21 t22))
          ≡⟨ sym (apCompose (branch t21 t22)) ⟩
            ap (compose s' s) (branch t21 t22)
          ∎)
unify t1 (var x) with x ∉FV t1 | inspect (_∉FV_ x) t1
...               | true | [ q ] 
  =  match (singleton x t1) 
        (trans (singleton-∉FV t1 x t1 q) 
                (varSingleton x t1))
...              | false | [ p ] with t1
...                               | var y = match empty (≡-cong var (sym (xisy p)))
...                               | _     = nomatch
unify (var x) t2 with unify t2 (var x) 
...              | nomatch = nomatch
...              | match s p = match s (sym p)


-----------------------------------------------
{- Another agda version that returns a proof when checking whether 
   a variable is free in the term.  -}

data _∈_ : ℕ → Term → Set where 
  invar   : ∀{x} → x ∈ (var x)
  inleft  : ∀ {x t1 t2} → x ∈ t1 -> x ∈ (branch t1 t2)
  inright : ∀ {x t1 t2} → x ∈ t2 -> x ∈ (branch t1 t2)
  
invvar : ∀ {x y} -> x ∈ (var y) -> x ≡ y
invvar invar = refl


lemma : ∀ {x t1 t2} -> ¬ (x ∈ t1) -> ¬ (x ∈ t2) -> ¬ (x ∈ (branch t1 t2))
lemma ¬p ¬q (inleft x) = ¬p x
lemma ¬p ¬q (inright x) = ¬q x

_is∈_ : (x : ℕ) -> (t : Term) -> Dec (x ∈ t)
x is∈ leaf = no (\ ())
x is∈ (branch t1 t2) with (x is∈ t1) | (x is∈ t2) 
... | yes p  | _      = yes (inleft p)
... | no _   | yes q  = yes (inright q)
... | no ¬p  | no ¬q  = no  (lemma ¬p ¬q)
x is∈ (var y) with (x ≟ y) 
.x is∈ (var x) | yes refl = yes invar
...            | no ¬p    = no (¬p ∘ invvar)

-- interaction between singleton and ∈ 

singleton-∉ : ∀ t x s → ¬ (x ∈ t) → ap (singleton x s) t ≡ t
singleton-∉ leaf x s = λ _ →  refl
singleton-∉ (branch t1 t2) x s with (x is∈ t1) | (x is∈ t2)
...                                | yes p | _     = λ br -> ⊥-elim (br (inleft p))
...                                | no  _ | yes p = λ br -> ⊥-elim (br (inright p))
...                                | no p1 | no  p2 = λ _ → cong₂ branch (singleton-∉ t1 x s p1) 
                                                                         (singleton-∉ t2 x s p2) 
singleton-∉ (var y) x s with (x ≟ y) 
singleton-∉ (var .x) x s | (yes refl) = λ br -> ⊥-elim (br invar)
...                      | (no ¬p)    = λ _ → refl

{-# NO_TERMINATION_CHECK #-}
unify' : (t1 t2 : Term) → Unify t1 t2
unify' leaf leaf = match empty refl
unify' leaf (branch t2 t3) = nomatch
unify' (branch t1 t2) leaf = nomatch
unify' (branch t11 t12) (branch t21 t22) 
      with unify' t11 t21 
...    | nomatch = nomatch
...    | match s p with unify' (ap s t12) (ap s t22) 
...               | nomatch = nomatch
...               | match s' q 
  =  match (compose s' s) 
         (begin
            ap (compose s' s) (branch t11 t12)
          ≡⟨ apCompose (branch t11 t12)  ⟩
            ap s' (ap s (branch t11 t12))
          ≡⟨ refl ⟩
            branch (ap s' (ap s t11)) (ap s' (ap s t12))
          ≡⟨ cong₂ (λ t1 t2 → branch (ap s' t1) t2) p q ⟩
            branch (ap s' (ap s t21)) (ap s' (ap s t22))
          ≡⟨ refl ⟩
             ap s' (ap s (branch t21 t22))
          ≡⟨ sym (apCompose (branch t21 t22)) ⟩
            ap (compose s' s) (branch t21 t22)
          ∎)
unify' t (var x) with (x is∈ t)
...               | no q  -- proof that ¬ (x ∈ t)
  =  match (singleton x t) 
         (begin
            ap (singleton x t) t
          ≡⟨ singleton-∉ t x t q  ⟩
            t
          ≡⟨ varSingleton x t  ⟩
            ap (singleton x t) (var x)
          ∎)
...              | yes p with t 
...                      | var y = match empty (≡-cong var (sym (invvar p)))
...                      | _     = nomatch
unify' (var x) t with unify' t (var x) 
...              | nomatch = nomatch
...              | match s p = match s (sym p)

-- version actually in the paper. Compresses the equation chains above

{-# NO_TERMINATION_CHECK #-}
unify'' : (t1 t2 : Term) → Unify t1 t2
unify'' leaf leaf = match empty refl
unify'' leaf (branch t2 t3) = nomatch
unify'' (branch t1 t2) leaf = nomatch
unify'' (branch t11 t12) (branch t21 t22) 
      with unify'' t11 t21 
...     | nomatch = nomatch
...     | match s p with unify'' (ap s t12) (ap s t22) 
...                 | nomatch = nomatch
...                 | match s' q 
  =  match (compose s' s) 
           (trans (apCompose (branch t11 t12))
           (trans (cong₂ (λ t1 t2 → branch (ap s' t1) t2) p q)
                  (sym (apCompose (branch t21 t22)))))
unify'' t1 (var x) with (x is∈ t1)
...               | no q  -- proof that ¬ (x ∈ t)
  =  match (singleton x t1) 
           (trans (singleton-∉ t1 x t1 q) 
                  (varSingleton x t1))
...              | yes p with t1 
...                      | var y = match empty (cong var (sym (invvar p)))
...                      | _      = nomatch
unify'' (var x) t2 with unify'' t2 (var x) 
...              | nomatch = nomatch
...              | match s p = match s (sym p)
