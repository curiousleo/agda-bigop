module Bigop.Filter where

open import Bigop.Ordinals

open import Data.List.Base using (List; _∷_; [])
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred; Decidable; ∁)

infixl 5 _∥_

_∥_ : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → List I → Decidable P → List I
[]       ∥ dec = []
(i ∷ is) ∥ dec with dec i
(i ∷ is) ∥ dec | yes _ = i ∷ (is ∥ dec)
(i ∷ is) ∥ dec | no  _ =      is ∥ dec

-- equivalent to `filter (⌊_⌋ ∘ dec) is`

∁′ : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → Decidable P → Decidable (∁ P)
∁′ p x with p x
∁′ p x | yes q = no (λ ¬q → ¬q q)
∁′ p x | no ¬q = yes (λ q → ¬q q)

private
 module Test where

  open import Bigop.Ordinals
  open import Bigop.Filter.Predicates

  open import Relation.Binary.PropositionalEquality

  test-even : (upFromℕ 1 6) ∥ even ≡ 2 ∷ 4 ∷ 6 ∷ []
  test-even = refl

  test-odd : (upFromℕ 1 6) ∥ odd ≡ 1 ∷ 3 ∷ 5 ∷ []
  test-odd = refl
