-- this is like Unify.agda, but instead of the unify function taking σ as an input,
-- it eagerly applies the substitution as it goes along. This is slower, but makes the 
-- proof simpler.
module UnifyEager where

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

_/_ : Term -> Substitution -> Term
leaf / σ = leaf
branch t1 t2 / σ = branch (t1 / σ) (t2 / σ)
var x / σ with σ x
...         | (just t) =  t
...         | (nothing) = var x

-- Composing subsitutions
_•_ : Substitution → Substitution → Substitution
_•_ σ1 σ2 x with σ1 x
...           | just t = just (t / σ2)
...           | nothing = σ2 x

/• : ∀ {σ σ'} → (t : Term) → t / (σ • σ') ≡ (t / σ) / σ'
/• leaf = refl
/• (branch t1 t2) = cong₂ branch (/• t1) (/• t2)
/• {σ1} (var x) with σ1 x 
...               | just t' = refl
...               | nothing = refl

var/singleton : ∀ x t → t ≡ var x / (singleton x t)
var/singleton x t with x ≟ x 
var/singleton x t | yes p =  refl
var/singleton x t | no ¬p = ⊥-elim (¬p refl)

singleton-∉FV : ∀ t x s → (x ∉FV t) ≡ true →( t / singleton x s) ≡ t
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
  yes : ∀{t1 t2} (σ : Substitution) → (t1 / σ) ≡ (t2 / σ) → Unify t1 t2

Unify-sym : ∀{t1 t2} → Unify t1 t2 → Unify t2 t1
Unify-sym no = no
Unify-sym (yes σ q) = yes σ (sym q)

{- Some slightly tricky points, which came out of the proof:
    * We need the occurs check for correctness; since our definition of 
       applying a substitution only applies it once. 
 -}

{-# NO_TERMINATION_CHECK #-}
unify : (t1 t2 : Term) → Unify t1 t2
unify leaf leaf = yes empty refl
unify leaf (branch t2 t3) = no
unify (branch t1 t2) leaf = no
unify (branch t11 t12) (branch t21 t22) 
      with unify t11 t21 
... | no = no
... | yes σ p with unify (t12 / σ) (t22 / σ) 
...               | no = no
...               | yes σ' q =  yes (σ • σ') 
                                     (begin
                                        branch t11 t12 / (σ • σ') 
                                      ≡⟨ /• (branch t11 t12)  ⟩
                                        (branch t11 t12 / σ) / σ'
                                      ≡⟨ refl  ⟩
                                        branch ((t11 / σ) / σ') ((t12 / σ) / σ')
                                      ≡⟨ cong₂ (λ s t → branch (s / σ') t) p q ⟩
                                        branch ((t21 / σ) / σ') ((t22 / σ) / σ')
                                      ≡⟨ refl ⟩
                                        (branch t21 t22 / σ) / σ'
                                      ≡⟨ sym (/• (branch t21 t22)) ⟩
                                        branch t21 t22 / (σ • σ')
                                      ∎ )
unify t (var x) with x ∉FV t | inspect (_∉FV_ x) t
...                          | true | [ q ] =  yes (singleton x t) 
                                                   (begin
                                                      t / singleton x t
                                                    ≡⟨ singleton-∉FV t x t q  ⟩
                                                      t
                                                    ≡⟨ var/singleton x t  ⟩
                                                      var x / singleton x t
                                                    ∎)
...                          | false | _ =  no
unify (var x) t = Unify-sym (unify t (var x))
