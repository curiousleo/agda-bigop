module Bigop.Ordinals where

open import Data.List hiding (_∷ʳ_)
open import Data.Fin hiding (_≤_; _+_; lift)
open import Data.Nat
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc)
open import Function using (_∘_)

upFromℕ : ℕ → ℕ → List ℕ
upFromℕ from zero = []
upFromℕ from (suc len) = from ∷ upFromℕ (suc from) len

upFromF : (from len : ℕ) → List (Fin (from + len))
upFromF from zero = []
upFromF from (suc len) rewrite +-suc from len = fromℕ≤ {from} (s≤s (m≤m+n from len)) ∷ upFromF (suc from) len
