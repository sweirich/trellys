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
  leaf : Term
  branch : Term → Term → Term
  var  : ℕ → Term

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

ap : Substitution → Term  → Term
ap σ leaf = leaf
ap σ (branch t1 t2) = branch (ap σ t1) (ap σ t2)
ap σ (var x) with σ x
...         | (just t) =  t
...         | (nothing) = var x

-- Composing subsitutions
compose : Substitution → Substitution → Substitution
compose σ1 σ2 x with σ2 x
...           | just t = just (ap σ1 t)
...           | nothing = σ1 x

apCompose : ∀ {σ σ'} → (t : Term) → ap (compose σ σ') t  ≡ ap σ (ap σ' t)
apCompose leaf = refl
apCompose (branch t1 t2) = cong₂ branch (apCompose t1) (apCompose t2)
apCompose {σ} {σ'} (var x) with σ' x 
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
  yes : ∀{t1 t2} (σ : Substitution) → ap σ t1 ≡ ap σ t2 → Unify t1 t2   

{-# NO_TERMINATION_CHECK #-}
unify : (t1 t2 : Term) → Unify t1 t2
unify leaf leaf = yes empty refl
unify leaf (branch t2 t3) = no
unify (branch t1 t2) leaf = no
unify (branch t11 t12) (branch t21 t22) 
      with unify t11 t21 
... | no = no
... | yes σ p with unify (ap σ t12) (ap σ t22) 
...               | no = no
...               | yes σ' q =  yes (compose σ' σ) 
                                    (begin
                                       ap (compose σ' σ) (branch t11 t12)
                                     ≡⟨ apCompose (branch t11 t12)  ⟩
                                       ap σ' (ap σ (branch t11 t12))
                                     ≡⟨ refl  ⟩
                                       branch (ap σ' (ap σ t11)) (ap σ' (ap σ t12))
                                     ≡⟨ cong₂ (λ s t → branch (ap σ' s) t) p q ⟩
                                       branch (ap σ' (ap σ t21)) (ap σ' (ap σ t22))
                                     ≡⟨ refl ⟩
                                       ap σ' (ap σ (branch t21 t22))
                                     ≡⟨ sym (apCompose (branch t21 t22)) ⟩
                                       ap (compose σ' σ) (branch t21 t22)
                                     ∎ )
unify t (var x) with x ∉FV t | inspect (_∉FV_ x) t
...                | true | [ q ] =  yes (singleton x t) 
                                         (begin
                                            ap (singleton x t) t
                                          ≡⟨ singleton-∉FV t x t q  ⟩
                                            t
                                          ≡⟨ varSingleton x t  ⟩
                                            ap (singleton x t) (var x)
                                          ∎)
...                          | false | _ =  no
unify (var x) t with unify t (var x) 
...                | no = no
...                | yes σ p = yes σ (sym p)
