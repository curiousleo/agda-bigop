module Bigop.Core where

open import Algebra

module Fold {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

  open import Data.List using (List; foldr)

  open Monoid M renaming (Carrier to R)

  fold : (I → R) → List I → R
  fold f = foldr (λ x y → (f x) ∙ y) ε

  Σ-syntax = fold
  syntax Σ-syntax (λ x → e) v = Σ[ x ← v $ e ]

  Π-syntax = fold
  syntax Π-syntax (λ x → e) v = Π[ x ← v $ e ]

  ⨁-syntax = fold
  syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v $ e ]

  ⨂-syntax = fold
  syntax ⨂-syntax (λ x → e) v = ⨂[ x ← v $ e ]

module FoldNonEmpty {c ℓ} (S : Semigroup c ℓ) {i} {I : Set i} where

  open import Data.List.NonEmpty using (List⁺; foldr)

  open Semigroup S renaming (Carrier to R)

  fold : (I → R) → List⁺ I → R
  fold f = foldr (λ x y → (f x) ∙ y) f

  ⋁-syntax = fold
  syntax ⋁-syntax (λ x → e) v = ⋁[ x ← v $ e ]

  ⋀-syntax = fold
  syntax ⋀-syntax (λ x → e) v = ⋀[ x ← v $ e ]
