------------------------------------------------------------------------
-- Big operator library
--
-- Core definitions: crush, fold and syntax
------------------------------------------------------------------------

module Bigop.Core where

open import Algebra
open import Function using (_∘_; id)

------------------------------------------------------------------------
-- Folding over monoids

module Fold {c ℓ} (M : Monoid c ℓ) where

  open import Data.List.Base using (List; foldr; map)

  open Monoid M renaming (Carrier to R)

  crush : List R → R
  crush = foldr _∙_ ε

  fold : ∀ {i} → {I : Set i} → (I → R) → List I → R
  fold f = crush ∘ map f

  -- An equivalent definition would be
  --   fold f = foldr (λ x y → (f x) ∙ y) ε

  infix 6 Σ-syntax ⋁-syntax ⨁-syntax
  infix 5 Π-syntax ⋀-syntax ⨂-syntax

  Σ-syntax = fold
  syntax Σ-syntax (λ x → e) v = Σ[ x ← v ] e

  Π-syntax = fold
  syntax Π-syntax (λ x → e) v = Π[ x ← v ] e

  ⋁-syntax = fold
  syntax ⋁-syntax (λ x → e) v = ⋁[ x ← v ] e

  ⋀-syntax = fold
  syntax ⋀-syntax (λ x → e) v = ⋀[ x ← v ] e

  ⨁-syntax = fold
  syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v ] e

  ⨂-syntax = fold
  syntax ⨂-syntax (λ x → e) v = ⨂[ x ← v ] e

------------------------------------------------------------------------
-- Folding over semigroups

module FoldNonEmpty {c ℓ} (S : Semigroup c ℓ) {i} {I : Set i} where

  open import Data.List.NonEmpty using (List⁺; foldr₁; map)

  open Semigroup S renaming (Carrier to R)

  fold : (I → R) → List⁺ I → R
  fold f = crush ∘ map f
    where
      crush : List⁺ R → R
      crush = foldr₁ _∙_

  -- Equivalently,
  --   fold f = foldr (λ x y → (f x) ∙ y) f
