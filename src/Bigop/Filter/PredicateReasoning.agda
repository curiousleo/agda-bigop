module Bigop.Filter.PredicateReasoning where

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.Core hiding (Decidable)
open import Relation.Binary.EqReasoning using (_IsRelatedTo_)
open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_; _≡⟨_⟩_)
open import Relation.Binary hiding (Decidable)

open Setoid

infixr 2 _≈⌊_∈_⌋⟨_⟩⟨_⟩_ _≡⌊_∈_⌋⟨_⟩⟨_⟩_

_≈⌊_∈_⌋⟨_⟩⟨_⟩_ : ∀ {c ℓ₁} {S : Setoid c ℓ₁} {i ℓ₂} {I : Set i} {P : Pred I ℓ₂}
                 (x : Carrier S) (i : I) (dec : Decidable P) {y z : Carrier S} →
                 ((P i) → _≈_ S x y) → ((¬ P i) → _≈_ S x y) →
                 _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
x ≈⌊ i ∈ dec ⌋⟨ y ⟩⟨ n ⟩ r with dec i
x ≈⌊ i ∈ dec ⌋⟨ y ⟩⟨ n ⟩ r | yes pi = x ≈⟨ y  pi ⟩ r
x ≈⌊ i ∈ dec ⌋⟨ y ⟩⟨ n ⟩ r | no ¬pi = x ≈⟨ n ¬pi ⟩ r

_≡⌊_∈_⌋⟨_⟩⟨_⟩_ : ∀ {c ℓ₁} {S : Setoid c ℓ₁} {i ℓ₂} {I : Set i} {P : Pred I ℓ₂}
                 (x : Carrier S) (i : I) (dec : Decidable P) {y z : Carrier S} →
                 ((P i) → _≡_ x y) → ((¬ P i) → _≡_ x y) →
                 _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
x ≡⌊ i ∈ dec ⌋⟨ y ⟩⟨ n ⟩ r with dec i
x ≡⌊ i ∈ dec ⌋⟨ y ⟩⟨ n ⟩ r | yes pi = x ≡⟨ y  pi ⟩ r
x ≡⌊ i ∈ dec ⌋⟨ y ⟩⟨ n ⟩ r | no ¬pi = x ≡⟨ n ¬pi ⟩ r

infixr 2 _≈⌊_~_by_⌋⟨_⟩⟨_⟩⟨_⟩_ _≡⌊_~_by_⌋⟨_⟩⟨_⟩⟨_⟩_

_≈⌊_~_by_⌋⟨_⟩⟨_⟩⟨_⟩_ : ∀ {c ℓ₁} {S : Setoid c ℓ₁}
                       {i ℓ₂ ℓ₃} {I : Set i} {_~_ : Rel I ℓ₂ } {_<_ : Rel I ℓ₃}
                       (x : Carrier S) (i j : I) (tri : Trichotomous _~_ _<_)
                       {y z : Carrier S} →
                       (  i < j → ¬ i ~ j → ¬ j < i → _≈_ S x y) →
                       (¬ i < j →   i ~ j → ¬ j < i → _≈_ S x y) →
                       (¬ i < j → ¬ i ~ j →   j < i → _≈_ S x y) →
                       _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
x ≈⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r with t i j
x ≈⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r | tri< a ¬b ¬c = x ≈⟨ eq< a ¬b ¬c ⟩ r
x ≈⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r | tri≈ ¬a b ¬c = x ≈⟨ eq~ ¬a b ¬c ⟩ r
x ≈⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r | tri> ¬a ¬b c = x ≈⟨ eq> ¬a ¬b c ⟩ r

_≡⌊_~_by_⌋⟨_⟩⟨_⟩⟨_⟩_ : ∀ {c ℓ₁} {S : Setoid c ℓ₁}
                       {i ℓ₂ ℓ₃} {I : Set i} {_~_ : Rel I ℓ₂ } {_<_ : Rel I ℓ₃}
                       (x : Carrier S) (i j : I) (tri : Trichotomous _~_ _<_)
                       {y z : Carrier S} →
                       (  i < j → ¬ i ~ j → ¬ j < i → _≡_ x y) →
                       (¬ i < j →   i ~ j → ¬ j < i → _≡_ x y) →
                       (¬ i < j → ¬ i ~ j →   j < i → _≡_ x y) →
                       _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
x ≡⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r with t i j
x ≡⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r | tri< a ¬b ¬c = x ≡⟨ eq< a ¬b ¬c ⟩ r
x ≡⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r | tri≈ ¬a b ¬c = x ≡⟨ eq~ ¬a b ¬c ⟩ r
x ≡⌊ i ~ j by t ⌋⟨ eq< ⟩⟨ eq~ ⟩⟨ eq> ⟩ r | tri> ¬a ¬b c = x ≡⟨ eq> ¬a ¬b c ⟩ r
