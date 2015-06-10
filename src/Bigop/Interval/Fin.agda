------------------------------------------------------------------------
-- Big operator library
--
-- Intervals of finite sets
------------------------------------------------------------------------

module Bigop.Interval.Fin where

open import Data.List.Base
open import Data.Fin using (Fin; fromℕ≤)
open import Data.Nat.Base
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc)

upFrom : (from len : ℕ) → List (Fin (from + len))
upFrom from zero = []
upFrom from (suc len)
  rewrite +-suc from len =
    fromℕ≤ {from} (s≤s (m≤m+n from len)) ∷ upFrom (suc from) len

range : ℕ → (to : ℕ) → List (Fin to)
range zero to = upFrom zero to
range (suc from) to = tail (range from to)
  where
    tail : ∀ {a} {A : Set a} → List A → List A
    tail [] = []
    tail (x ∷ xs) = xs

infix 6 _…<_ _…_

_…<_ = range

_…_ : ℕ → (to : ℕ) → List (Fin (suc to))
from … to = range from (suc to)
