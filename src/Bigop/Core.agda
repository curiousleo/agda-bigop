module Bigop.Core where

open import Algebra

module Fold {c ℓ} (M : Monoid c ℓ) where

  open import Data.List.Base using (List; foldr; map)
  open import Function using (_∘_)

  open Monoid M renaming (Carrier to R)

  crush : List R → R
  crush = foldr _∙_ ε

  fold : ∀ {i} → {I : Set i} → (I → R) → List I → R
  fold f = crush ∘ map f

  -- An equivalent definition would be
  --   fold f = foldr (λ x y → (f x) ∙ y) ε

  infix 6 Σ-syntax ⨁-syntax
  infix 5 Π-syntax ⨂-syntax

  Σ-syntax = fold
  syntax Σ-syntax (λ x → e) v = Σ[ x ← v ] e

  Π-syntax = fold
  syntax Π-syntax (λ x → e) v = Π[ x ← v ] e

  ⨁-syntax = fold
  syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v ] e

  ⨂-syntax = fold
  syntax ⨂-syntax (λ x → e) v = ⨂[ x ← v ] e

module FoldNonEmpty {c ℓ} (S : Semigroup c ℓ) {i} {I : Set i} where

  open import Data.List.NonEmpty using (List⁺; foldr₁; map)
  open import Function using (_∘_; id)

  open Semigroup S renaming (Carrier to R)

  fold : (I → R) → List⁺ I → R
  fold f = crush ∘ map f
    where
      crush : List⁺ R → R
      crush = foldr₁ _∙_

  -- Equivalently,
  --   fold f = foldr (λ x y → (f x) ∙ y) f

  infix 6 ⋁-syntax
  infix 5 ⋀-syntax

  ⋁-syntax = fold
  syntax ⋁-syntax (λ x → e) v = ⋁[ x ← v ] e

  ⋀-syntax = fold
  syntax ⋀-syntax (λ x → e) v = ⋀[ x ← v ] e
