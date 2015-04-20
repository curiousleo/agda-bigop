module Bigop.Core.Properties where

import Bigop.Core as Core

open import Algebra

module Fold {c ℓ} (M : Monoid c ℓ) where

  open import Data.List
  open import Relation.Binary.PropositionalEquality

  open Monoid M using (_∙_; ε) renaming (Carrier to R)
  open Core.Fold M using (fold)

  crush : List R → R
  crush = foldr _∙_ ε

  crush∘map : ∀ {i} → {I : Set i} (f : I → R) (is : List I) →
              crush (map f is) ≡ fold f is
  crush∘map f []       = refl
  crush∘map f (i ∷ is) = cong (_∙_ (f i)) (crush∘map _ is)
