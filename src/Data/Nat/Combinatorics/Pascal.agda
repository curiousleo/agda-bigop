module Data.Nat.Combinatorics.Pascal where

open import Bigop.Core
open import Bigop.Interval.Nat

open import Algebra

open import Data.Nat
  using (zero; suc)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple as P
open import Data.Nat.Combinatorics.Combinatorics

open import Data.Product
  using (proj₁; proj₂)

open import Function

import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.SetoidReasoning

open CommutativeSemiring commutativeSemiring
  renaming (Carrier to ℕ)

open Fold (+-monoid)


