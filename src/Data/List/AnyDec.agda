module Data.List.AnyDec where

open import Data.List.Base
open import Data.List.Any
open import Relation.Nullary
open import Relation.Binary

module DecMembership {c ℓ} (S : DecSetoid c ℓ) where

  open DecSetoid S renaming (Carrier to A)
  open Membership setoid

  infix 4 _∈?_

  _∈?_ : Decidable _∈_
  x ∈? [] = no (λ ())
  x ∈? (y ∷ ys) with x ≟ y | x ∈? ys
  ... | yes x≈y | _        = yes (here x≈y)
  ... | no ¬x≈y | yes x∈ys = yes (there x∈ys)
  ... | no ¬x≈y | no ¬x∈ys = no contradiction
    where
      contradiction : ¬ Any (_≈_ x) (y ∷ ys)
      contradiction (here x≈y)   = ¬x≈y x≈y
      contradiction (there x∈ys) = ¬x∈ys x∈ys
