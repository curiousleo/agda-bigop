module Bigop.Ordinals where

open import Data.List.Base
open import Data.Fin using (Fin; fromℕ≤)
open import Data.Nat.Base
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc)

upFromℕ : ℕ → ℕ → List ℕ
upFromℕ from zero      = []
upFromℕ from (suc len) = from ∷ upFromℕ (suc from) len

upFromF : (from len : ℕ) → List (Fin (from + len))
upFromF from zero = []
upFromF from (suc len)
  rewrite +-suc from len =
    fromℕ≤ {from} (s≤s (m≤m+n from len)) ∷ upFromF (suc from) len
