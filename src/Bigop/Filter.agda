module Bigop.Filter where

open import Bigop.Ordinals

import Level

open import Data.List.Base
open import Relation.Nullary
open import Relation.Unary

infix 5 _∥_

_∥_ : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → List I → Decidable P → List I
[]       ∥ dec = []
(i ∷ is) ∥ dec with dec i
(i ∷ is) ∥ dec | yes _ = i ∷ (is ∥ dec)
(i ∷ is) ∥ dec | no  _ =      is ∥ dec

private
 module Test where

  open import Bigop.Ordinals
  open import Bigop.Filter.Predicates

  open import Relation.Binary.PropositionalEquality

  test-even : (1 … 6) ∥ even ≡ 2 ∷ 4 ∷ 6 ∷ []
  test-even = refl

  test-odd : (1 … 6) ∥ odd ≡ 1 ∷ 3 ∷ 5 ∷ []
  test-odd = refl
