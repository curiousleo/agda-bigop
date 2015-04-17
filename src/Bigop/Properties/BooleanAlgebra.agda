open import Algebra

module Bigop.Properties.BooleanAlgebra
       {c ℓ} (BA : BooleanAlgebra c ℓ) where

open import Bigop.Core

open import Data.List
open import Data.List.NonEmpty

open BooleanAlgebra BA renaming (Carrier to R)
import Algebra.Properties.BooleanAlgebra BA as P

open import Relation.Binary.EqReasoning setoid

∨-semigroup : Semigroup c ℓ
∨-semigroup = record
  { Carrier = R
  ; _≈_     = _≈_
  ; _∙_     = _∨_
  ; isSemigroup = record
    { isEquivalence = isEquivalence
    ; assoc         = ∨-assoc
    ; ∙-cong        = ∨-cong
    }
  }

∧-semigroup : Semigroup c ℓ
∧-semigroup = record
  { Carrier = R
  ; _≈_     = _≈_
  ; _∙_     = _∧_
  ; isSemigroup = record
    { isEquivalence = isEquivalence
    ; assoc         = ∧-assoc
    ; ∙-cong        = ∧-cong
    }
  }

open FoldNonEmpty ∨-semigroup using (⋁-syntax)
open FoldNonEmpty ∧-semigroup using (⋀-syntax)

deMorgan₂ : ∀ {i} → {I : Set i} → (f : I → R) → (idx : List⁺ I) →
            ¬ ⋁[ i ← idx $ f i ] ≈ ⋀[ i ← idx $ ¬ f i ]
deMorgan₂         f (x ∷ [])     = refl
deMorgan₂ {I = I} f (x ∷ y ∷ ys) = deMorgan₂′ f x y ys
  where
    deMorgan₂′ : ∀ (f : I → R) (x : I) (y : I) (ys : List I) →
          ¬ ⋁[ i ← (x ∷ y ∷ ys) $ f i ] ≈ ⋀[ i ← (x ∷ y ∷ ys) $ ¬ f i ]
    deMorgan₂′ f x y []       = P.deMorgan₂ _ _
    deMorgan₂′ f x y (z ∷ zs) = begin
      ¬ (f x ∨ ⋁[ i ← y ∷ z ∷ zs $ f i ])    ≈⟨ P.deMorgan₂ _ _ ⟩
      (¬ f x) ∧ ¬ ⋁[ i ← y ∷ z ∷ zs $ f i ]  ≈⟨ ∧-cong refl (deMorgan₂′ f y z zs) ⟩
      (¬ f x) ∧ ⋀[ i ← y ∷ z ∷ zs $ ¬ f i ]  ∎
