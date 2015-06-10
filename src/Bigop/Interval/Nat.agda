------------------------------------------------------------------------
-- Big operator library
--
-- Intervals of natural numbers
------------------------------------------------------------------------

module Bigop.Interval.Nat where

open import Data.List.Base
open import Data.Nat.Base

upFrom : ℕ → ℕ → List ℕ
upFrom from zero      = []
upFrom from (suc len) = from ∷ upFrom (suc from) len

range : ℕ → ℕ → List ℕ
range m n = upFrom m (n ∸ m)

infix 6 _…<_ _…_

_…<_ = range

_…_ : ℕ → ℕ → List ℕ
m … n = range m (suc n)
