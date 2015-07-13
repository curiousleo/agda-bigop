module Data.Fin.Countdown where

open import Data.Fin hiding (_≤_)
open import Data.Fin.Properties
open import Data.Nat.Base
open import Data.Nat.MoreProperties

data ⌛ {from} : (Fin (suc from)) → Set where
  start : ⌛ (fromℕ from)
  tick  : (m : Fin from) (ctd : ⌛ (suc m)) → ⌛ (inject₁ m)

⌛-≤ : ∀ {from rem} (ctd : ⌛ {from} rem) → toℕ rem ≤ from
⌛-≤ ctd = suc-inj (bounded _)

data ⌛′ {from} : ℕ → Set where
  start : ⌛′ from
  tick  : (r : ℕ) (ctd : ⌛′ {from} (suc r)) → ⌛′ r
