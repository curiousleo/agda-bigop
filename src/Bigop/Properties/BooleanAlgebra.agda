open import Algebra

module Bigop.Properties.BooleanAlgebra
       {c ℓ} (BA : BooleanAlgebra c ℓ) where

open import Bigop.Core

open import Data.List
open import Data.List.NonEmpty
open import Data.Product

open BooleanAlgebra BA renaming (Carrier to R)
import Algebra.Properties.BooleanAlgebra BA as P

open import Relation.Binary.EqReasoning setoid

open import Algebra.Properties.BooleanAlgebra BA
  using (∨-∧-commutativeSemiring; ¬⊥=⊤; ¬⊤=⊥)
open CommutativeSemiring ∨-∧-commutativeSemiring
  using () renaming (+-monoid to ∨-monoid; *-monoid to ∧-monoid)

open Fold ∨-monoid using (⋁-syntax)
open Fold ∧-monoid using (⋀-syntax)

deMorgan₁ : ∀ {i} → {I : Set i} → (f : I → R) → (idx : List I) →
            ¬ (⋀[ i ∈ idx ] f i) ≈ ⋁[ i ∈ idx ] ¬ f i
deMorgan₁ f [] = ¬⊤=⊥
deMorgan₁ f (x ∷ xs) = begin
  ¬ (f x ∧ (⋀[ i ∈ xs ] f i))    ≈⟨ P.deMorgan₁ _ _ ⟩
  (¬ f x) ∨ ¬ (⋀[ i ∈ xs ] f i)  ≈⟨ ∨-cong refl (deMorgan₁ f xs) ⟩
  (¬ f x) ∨ (⋁[ i ∈ xs ] ¬ f i)  ∎

deMorgan₂ : ∀ {i} → {I : Set i} → (f : I → R) → (idx : List I) →
            ¬ (⋁[ i ∈ idx ] f i) ≈ ⋀[ i ∈ idx ] ¬ f i
deMorgan₂ f [] = ¬⊥=⊤
deMorgan₂ f (x ∷ xs) = begin
  ¬ (f x ∨ ⋁[ i ∈ xs ] f i)      ≈⟨ P.deMorgan₂ _ _ ⟩
  (¬ f x) ∧ ¬ (⋁[ i ∈ xs ] f i)  ≈⟨ ∧-cong refl (deMorgan₂ f xs) ⟩
  (¬ f x) ∧ (⋀[ i ∈ xs ] ¬ f i)  ∎
