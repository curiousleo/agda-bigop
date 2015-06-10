------------------------------------------------------------------------
-- Big operator library
--
-- Decidable predicates for "even" and "odd"
------------------------------------------------------------------------

module Bigop.Filter.Predicates where

import Level

open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary
open import Relation.Unary

------------------------------------------------------------------------
-- Even

data Even : Pred ℕ Level.zero where
  zero-even : Even ℕ.zero
  ss-even   : ∀ {n} → Even n → Even (suc (suc n))

even : Decidable Even
even 0 = yes zero-even
even 1 = no (λ ())
even (suc (suc n)) with even n
... | yes p = yes (ss-even p)
... | no ¬p = no (ss-odd ¬p)
  where
    ss-odd : ∀ {n} → ¬ Even n → ¬ Even (suc (suc n))
    ss-odd ¬ps (ss-even p) = ¬ps p

------------------------------------------------------------------------
-- Odd

data Odd : Pred ℕ Level.zero  where
  one-odd : Odd 1
  ss-odd  : ∀ {n} → Odd n → Odd (suc (suc n))

odd : Decidable Odd
odd 0 = no (λ ())
odd 1 = yes one-odd
odd (suc (suc n)) with odd n
... | yes p = yes (ss-odd p)
... | no ¬p = no (ss-even′ ¬p)
  where
    ss-even′ : ∀ {n} → ¬ Odd n → ¬ Odd (suc (suc n))
    ss-even′ ¬ps (ss-odd p) = ⊥-elim (¬ps p)

------------------------------------------------------------------------
-- Additional rules

2n-even : ∀ n → Even (n + n)
2n-even zero = zero-even
2n-even (suc n) rewrite +-suc n n = ss-even (2n-even n)

even+1 : ∀ {n} → Even n → Odd (suc n)
even+1 zero-even        = one-odd
even+1 (ss-even even-n) = ss-odd (even+1 even-n)

even→¬odd : ∀ {n} → Even n → ¬ Odd n
even→¬odd zero-even        ()
even→¬odd (ss-even even-n) (ss-odd odd-n) = even→¬odd even-n odd-n
