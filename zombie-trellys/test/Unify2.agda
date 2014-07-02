module Unify2 where

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

plus_assoc : (i j k : ℕ) -> ((i + j) + k ≡ i + (j + k))
plus_assoc zero j k = refl
plus_assoc (suc i') j k = ≡-cong suc (plus_assoc i' j k)


isNo : ∀ {a} {P : Set a} → Dec P → Bool
isNo (yes _) = false
isNo (no _) =  true
 
data Term : Set where
  leaf   : Term
  branch : Term → Term → Term
  var    : ℕ → Term

injvar : ∀ {x y} -> var x ≡ var y -> x ≡ y
injvar refl = refl

injbr1  : ∀ {s1 s2 t1 t2} -> branch s1 t1 ≡ branch s2 t2 -> s1 ≡ s2
injbr1 refl = refl 

injbr2  : ∀ {s1 s2 t1 t2} -> branch s1 t1 ≡ branch s2 t2 -> t1 ≡ t2
injbr2 refl = refl 


-- returns true when x is not free in t
_∉FV_ : ℕ → Term → Bool
x ∉FV leaf = false
x ∉FV (branch t1 t2) = (x ∉FV t1) ∧ (x ∉FV t2)
x ∉FV (var y) with (x ≟ y)
...             | yes _ = false
...             | no _  = true

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

-- Composing subsitutions
compose : Substitution → Substitution → Substitution
compose s1 s2 x with s2 x
...           | just t = just (ap s1 t)
...           | nothing = s1 x

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

-- interaction between singleton and fv

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

data Unify : (t1 t2 : Term) → Set where
  nomatch  : ∀{t1 t2} → Unify t1 t2
  match : ∀{t1 t2} (s : Substitution) → ap s t1 ≡ ap s t2 → Unify t1 t2   

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
unify t (var x) with x ∉FV t | inspect (_∉FV_ x) t
...               | true | [ q ] 
  =  match (singleton x t) 
         (begin
            ap (singleton x t) t
          ≡⟨ singleton-∉FV t x t q  ⟩
            t
          ≡⟨ varSingleton x t  ⟩
            ap (singleton x t) (var x)
          ∎)
...              | false | _ =  nomatch
unify (var x) t with unify t (var x) 
...              | nomatch = nomatch
...              | match s p = match s (sym p)



{- Another agda version that returns a proof when checking whether 
   a variable is free in the term.  -}
data _∈_ : ℕ → Term → Set where 
  invar   : ∀{x} → x ∈ (var x)
  inleft  : ∀ {x t1 t2} → x ∈ t1 -> x ∈ (branch t1 t2)
  inright : ∀ {x t1 t2} → x ∈ t2 -> x ∈ (branch t1 t2)
  
invvar : ∀ {x y} -> x ∈ (var y) -> x ≡ y
invvar invar = refl

{-
invbranch : ∀ {x t1 t2} -> x ∈ (branch t1 t2) -> (x ∈ t1) ⊎ (x ∈ t2)
invbranch (inleft x) = inj₁ x
invbranch (inright x) = inj₂ x
-}

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
--            ap s' (ap s (branch t11 t12))
--          ≡⟨ refl ⟩
            branch (ap s' (ap s t11)) (ap s' (ap s t12))
          ≡⟨ cong₂ (λ t1 t2 → branch (ap s' t1) t2) p q ⟩
            branch (ap s' (ap s t21)) (ap s' (ap s t22))
--          ≡⟨ refl ⟩
--            ap s' (ap s (branch t21 t22))
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
...              | yes _ =  nomatch
unify' (var x) t with unify' t (var x) 
...              | nomatch = nomatch
...              | match s p = match s (sym p)


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
 {-        (begin
            ap (compose s' s) (branch t11 t12)
          ≡⟨ apCompose (branch t11 t12)  ⟩
--            ap s' (ap s (branch t11 t12))
--          ≡⟨ refl ⟩
            branch (ap s' (ap s t11)) (ap s' (ap s t12))
          ≡⟨ cong₂ (λ t1 t2 → branch (ap s' t1) t2) p q ⟩
            branch (ap s' (ap s t21)) (ap s' (ap s t22))
--          ≡⟨ refl ⟩
--            ap s' (ap s (branch t21 t22))
          ≡⟨ sym (apCompose (branch t21 t22)) ⟩
            ap (compose s' s) (branch t21 t22)
          ∎) -}
unify'' t (var x) with (x is∈ t)
...               | no q  -- proof that ¬ (x ∈ t)
  =  match (singleton x t) 
           (trans (singleton-∉ t x t q) 
                  (varSingleton x t))
{-         (begin
            ap (singleton x t) t
          ≡⟨ singleton-∉ t x t q  ⟩
            t
          ≡⟨ varSingleton x t  ⟩
            ap (singleton x t) (var x)
          ∎) -}
...              | yes _ =  nomatch
unify'' (var x) t with unify'' t (var x) 
...              | nomatch = nomatch
...              | match s p = match s (sym p)
