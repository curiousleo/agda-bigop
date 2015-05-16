module Bigop.Ordinals.Nat where

open import Data.List.Base
open import Data.Nat.Base

upFrom : ℕ → ℕ → List ℕ
upFrom from zero      = []
upFrom from (suc len) = from ∷ upFrom (suc from) len

range : ℕ → ℕ → List ℕ
range m n = upFrom m (n ∸ m)

_…<_ = range

_…_ : ℕ → ℕ → List ℕ
m … n = range m (suc n)
