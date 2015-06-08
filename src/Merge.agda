open import Algebra

module Merge
       {c ℓ} (M : CommutativeMonoid c ℓ) where

open import Bigop.Core
import Bigop.Properties.Monoid as MonoidProps

open import Data.List.Base
open import Data.Product hiding (map; swap)
open import Function
open import Relation.Nullary
open import Relation.Unary

open CommutativeMonoid M renaming (Carrier to R; _∙_ to _⊕_; ∙-cong to ⊕-cong)
open MonoidProps {c} {ℓ} monoid hiding (identity) public

open import Relation.Binary.EqReasoning setoid
open Fold monoid

merge : ∀ {i} {I : Set i} (f g : I → R) (is : List I) →
        (⨁[ i ← is ] f i) ⊕ (⨁[ i ← is ] g i) ≈ ⨁[ i ← is ] (f i ⊕ g i)
merge _ _ [] = proj₁ identity _
merge a b (i ∷ is) = begin
  (a i ⊕ (⨁[ i ← is ] a i)) ⊕ (b i ⊕ (⨁[ i ← is ] b i))  ≈⟨ assoc _ _ _ ⟩
  a i ⊕ ((⨁[ i ← is ] a i) ⊕ (b i ⊕ (⨁[ i ← is ] b i)))  ≈⟨ refl ⟨ ⊕-cong ⟩ lemma (b i) ⟩
  a i ⊕ (b i ⊕ (⨁[ i ← is ] a i ⊕ b i))                   ≈⟨ sym $ assoc _ _ _ ⟩
  (a i ⊕ b i) ⊕ (⨁[ i ← is ] a i ⊕ b i)                   ∎
  where
    lemma : ∀ x → (⨁[ i ← is ] a i) ⊕ (x ⊕ (⨁[ i ← is ] b i )) ≈
                  x ⊕ (⨁[ i ← is ] a i ⊕ b i)
    lemma x = begin
      (⨁[ i ← is ] a i) ⊕ (x ⊕ (⨁[ i ← is ] b i))  ≈⟨ sym $ assoc _ _ _ ⟩
      ((⨁[ i ← is ] a i) ⊕ x) ⊕ (⨁[ i ← is ] b i)  ≈⟨ comm _ _ ⟨ ⊕-cong ⟩ refl ⟩
      (x ⊕ (⨁[ i ← is ] a i)) ⊕ (⨁[ i ← is ] b i)  ≈⟨ assoc _ _ _ ⟩
      x ⊕ ((⨁[ i ← is ] a i) ⊕ (⨁[ i ← is ] b i))  ≈⟨ refl ⟨ ⊕-cong ⟩ merge a b is ⟩
      x ⊕ (⨁[ i ← is ] a i ⊕ b i)                   ∎


