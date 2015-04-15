module Bigop.Filter.Predicates where

import Level

open import Data.Empty
open import Data.Nat.Base
open import Relation.Nullary
open import Relation.Unary

data Even : Pred ℕ Level.zero where
  zero-even : Even ℕ.zero
  ss-even   : ∀ {n} → Even n → Even (suc (suc n))

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
  ss-odd  : ∀ {n} → Odd n → Odd (suc (suc n))

odd : Decidable Odd
odd 0 = no (λ ())
odd 1 = yes one-odd
odd (suc (suc n)) with odd n
odd (suc (suc n)) | yes p = yes (ss-odd p)
odd (suc (suc n)) | no ¬p = no (ss-even′ ¬p)
  where
    ss-even′ : ∀ {n} → ¬ Odd n → ¬ Odd (suc (suc n))
    ss-even′ ¬ps (ss-odd p) = ⊥-elim (¬ps p)
