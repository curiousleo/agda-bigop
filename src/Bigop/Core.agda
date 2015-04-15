module Bigop.Core where

open import Algebra
open import Data.List using (List; foldr)

module Fold {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

  open Monoid M renaming (Carrier to R)

  fold : (I → R) → List I → R
  fold f = foldr (λ x y → (f x) ∙ y) ε

  Σ-syntax : _
  Σ-syntax = fold

  syntax Σ-syntax (λ x → e) v = Σ[ x ← v $ e ]

  Π-syntax : _
  Π-syntax = fold

  syntax Π-syntax (λ x → e) v = Π[ x ← v $ e ]

  ⨁-syntax : _
  ⨁-syntax = fold

  syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v $ e ]

  ⨂-syntax : _
  ⨂-syntax = fold

  syntax ⨂-syntax (λ x → e) v = ⨂[ x ← v $ e ]
