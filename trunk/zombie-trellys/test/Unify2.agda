module Unify2 where

open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

open ≡-Reasoning

isNo : ∀ {a} {P : Set a} → Dec P → Bool
isNo (yes _) = false
isNo (no _) =  true
 
data Term : Set where
  leaf   : Term
  branch : Term → Term → Term
  var    : ℕ → Term

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
  no  : ∀{t1 t2} → Unify t1 t2
  yes : ∀{t1 t2} (s : Substitution) → ap s t1 ≡ ap s t2 → Unify t1 t2   

{-# NO_TERMINATION_CHECK #-}
unify : (t1 t2 : Term) → Unify t1 t2
unify leaf leaf = yes empty refl
unify leaf (branch t2 t3) = no
unify (branch t1 t2) leaf = no
unify (branch t11 t12) (branch t21 t22) 
      with unify t11 t21 
...    | no = no
...    | yes s p with unify (ap s t12) (ap s t22) 
...               | no = no
...               | yes s' q 
  =  yes (compose s' s) 
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
  =  yes (singleton x t) 
         (begin
            ap (singleton x t) t
          ≡⟨ singleton-∉FV t x t q  ⟩
            t
          ≡⟨ varSingleton x t  ⟩
            ap (singleton x t) (var x)
          ∎)
...              | false | _ =  no
unify (var x) t with unify t (var x) 
...              | no = no
...              | yes s p = yes s (sym p)
