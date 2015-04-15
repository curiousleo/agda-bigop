module Bigop.Filter where

open import Bigop.Ordinals

import Level

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Unary

DecPred : ∀ {i} (I : Set i) {ℓ} → Set _
DecPred I {ℓ} = Σ (Pred I ℓ) Decidable

infixl 6 _∣_ _∥_

_∣_ : ∀ {i} {I : Set i} {ℓ} → List I → DecPred I {ℓ} → List I
--  is ∣ (_ , dec) = filter (λ i → ⌊ dec i ⌋) is
[]       ∣ (_ , dec) = []
(i ∷ is) ∣ (_ , dec) with dec i
(i ∷ is) ∣ (p , dec) | yes _ = i ∷ is ∣ (p , dec)
(i ∷ is) ∣ (p , dec) | no  _ =     is ∣ (p , dec)

_∥_ : ∀ {i} {I : Set i} {ℓ} {P : Pred I ℓ} → List I → Decidable P → List I
[] ∥ dec = []
(i ∷ is) ∥ dec with dec i
(i ∷ is) ∥ dec | yes _ = i ∷ is ∥ dec
(i ∷ is) ∥ dec | no  _ =     is ∥ dec

data Even : Pred ℕ Level.zero where
  zero-even : Even ℕ.zero
  ss-even : ∀ {n} → Even n → Even (suc (suc n))

even : Decidable Even
even 0 = yes zero-even
even 1 = no (λ ())
even (suc (suc n)) with even n
even (suc (suc n)) | yes p = yes (ss-even p)
even (suc (suc n)) | no ¬p = no (ss-odd ¬p)
  where
    ss-odd : ∀ {n} → ¬ Even n → ¬ Even (suc (suc n))
    ss-odd ¬ps (ss-even p) = ⊥-elim (¬ps p)

data Odd : Pred ℕ Level.zero  where
  one-odd : Odd 1
  ss-odd : ∀ {n} → Odd n → Odd (suc (suc n))

odd : Decidable Odd
odd 0 = no (λ ())
odd 1 = yes one-odd
odd (suc (suc n)) with odd n
odd (suc (suc n)) | yes p = yes (ss-odd p)
odd (suc (suc n)) | no ¬p = no (ss-even′ ¬p)
  where
    ss-even′ : ∀ {n} → ¬ Odd n → ¬ Odd (suc (suc n))
    ss-even′ ¬ps (ss-odd p) = ⊥-elim (¬ps p)

even′ : DecPred ℕ {Level.zero}
even′ = Even , even

odd′ : DecPred ℕ {Level.zero}
odd′ = ∁ (proj₁ even′) , ¬? ∘ proj₂ even′
  where
    open import Relation.Nullary.Negation

open import Bigop.Ordinals

private
 module Test where

  open import Relation.Binary.PropositionalEquality

  test-even′ : 1 … 6 ∣ even′ ≡ 2 ∷ 4 ∷ 6 ∷ []
  test-even′ = refl

  test-odd′ : 1 … 6 ∣ odd′ ≡ 1 ∷ 3 ∷ 5 ∷ []
  test-odd′ = refl

  test-even : 1 … 6 ∥ even ≡ 2 ∷ 4 ∷ 6 ∷ []
  test-even = refl

  test-odd : 1 … 6 ∥ odd ≡ 1 ∷ 3 ∷ 5 ∷ []
  test-odd = refl
