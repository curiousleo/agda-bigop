module Dijkstra.Algebra.Properties where

open import Data.Product
open import Data.Sum
open import Relation.Binary
import Dijkstra.Algebra.FunctionProperties as FunctionProperties
open import Algebra.FunctionProperties.Core using (Op₂)
open import Dijkstra.Algebra

rightCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
rightCanonicalOrder _≈_ _∙_ a b = ∃ λ c → b ≈ (a ∙ c)

leftCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
leftCanonicalOrder _≈_ _∙_ a b = ∃ λ c → a ≈ (b ∙ c)

module RequiresDijkstraAlgebra
       {c ℓ} (dijkstra : DijkstraAlgebra c ℓ) where

  open DijkstraAlgebra dijkstra
  open FunctionProperties _≈_

  _⊴ᴸ_ = leftCanonicalOrder _≈_ _+_

  +-idempotent : Idempotent _+_
  +-idempotent x with +-selective x x
  ... | inj₁ eq = eq
  ... | inj₂ eq = eq

--  equivalent : ∀ a b → a + b ≈ b → a ⊴ b
--  equivalent a b a+b≈b = b , (sym a+b≈b)

  isRightIncreasing : ∀ a b → a ⊴ᴸ (a * b)
  isRightIncreasing a b = a , trans (sym (+-absorbs-* a b)) (+-comm _ _)

module RequiresCommutativeMonoid
       {c ℓ} (cmon : CommutativeMonoid c ℓ) where

  open CommutativeMonoid cmon
  open FunctionProperties _≈_
  open import Relation.Binary.EqReasoning setoid

  _⊴ᴸ_ = leftCanonicalOrder _≈_ _∙_
  _⊴ᴿ_ = rightCanonicalOrder _≈_ _∙_

  isTotalOrderᴸ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴸ_
  isTotalOrderᴸ selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴ᴸ-reflexive
              ; trans = ⊴ᴸ-transitive
              }
          ; antisym = ⊴ᴸ-antisym
          }
      ; total = total
    }
    where
      ⊴ᴸ-reflexive : _≈_ ⇒ _⊴ᴸ_
      ⊴ᴸ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity b) (sym a≈b))

      ⊴ᴸ-transitive : Transitive _⊴ᴸ_
      ⊴ᴸ-transitive {a} {b} {c} (x , a≈b∙x) (y , b≈c∙y) = x ∙ y , eq
        where
          eq =
            begin
              a            ≈⟨ a≈b∙x ⟩
              b ∙ x        ≈⟨ ∙-cong b≈c∙y refl ⟩
              (c ∙ y) ∙ x  ≈⟨ assoc _ _ _ ⟩
              c ∙ (y ∙ x)  ≈⟨ ∙-cong refl (comm _ _) ⟩
              c ∙ (x ∙ y)
            ∎

      ⊴ᴸ-antisym : Antisymmetric _≈_ _⊴ᴸ_
      ⊴ᴸ-antisym {a} {b} (x , a≈b∙x) (y , b≈a∙y) with selective a y | selective b x
      ... | _          | inj₁ b∙x≈b = trans a≈b∙x b∙x≈b
      ... | inj₁ a∙y≈a | _          = sym (trans b≈a∙y a∙y≈a)
      ... | inj₂ a∙y≈y | inj₂ b∙x≈x = a≈b
        where
          a≈x = trans a≈b∙x b∙x≈x
          b≈y = trans b≈a∙y a∙y≈y
          a≈b =
            begin
              a ≈⟨ a≈x ⟩
              x ≈⟨ sym b∙x≈x ⟩
              b ∙ x ≈⟨ ∙-cong b≈y refl ⟩
              y ∙ x ≈⟨ comm _ _ ⟩
              x ∙ y ≈⟨ ∙-cong (sym a≈x) refl ⟩
              a ∙ y ≈⟨ a∙y≈y ⟩
              y ≈⟨ sym b≈y ⟩
              b
            ∎

      total : Total _⊴ᴸ_
      total x y with selective x y
      ... | inj₁ ≈x = inj₁ (x , (sym (trans (comm _ _) ≈x)))
      ... | inj₂ ≈y = inj₂ (y , (sym ≈y))


  isTotalOrderᴿ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴿ_
  isTotalOrderᴿ selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴ᴿ-reflexive
              ; trans = ⊴ᴿ-transitive
              }
          ; antisym = ⊴ᴿ-antisym
          }
      ; total = total
    }
    where
      ⊴ᴿ-reflexive : _≈_ ⇒ _⊴ᴿ_
      ⊴ᴿ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity a) a≈b)

      ⊴ᴿ-transitive : Transitive _⊴ᴿ_
      ⊴ᴿ-transitive {a} {b} {c} (x , b≈a∙x) (y , c≈b∙y) =
        x ∙ y , trans c≈b∙y (trans (∙-cong b≈a∙x refl) (assoc _ _ _))

      ⊴ᴿ-antisym : Antisymmetric _≈_ _⊴ᴿ_
      ⊴ᴿ-antisym {a} {b} (x , b≈a∙x) (y , a≈b∙y) with selective a x | selective b y
      ... | _          | inj₁ b∙y≈b = trans a≈b∙y b∙y≈b
      ... | inj₁ a∙x≈a | _          = sym (trans b≈a∙x a∙x≈a)
      ... | inj₂ a∙x≈x | inj₂ b∙y≈y = a≈b
        where
          a≈y = trans a≈b∙y b∙y≈y
          b≈x = trans b≈a∙x a∙x≈x
          a≈b =
            begin
              a      ≈⟨ a≈y ⟩
              y      ≈⟨ sym b∙y≈y ⟩
              b ∙ y  ≈⟨ ∙-cong b≈x refl ⟩
              x ∙ y  ≈⟨ comm _ _ ⟩
              y ∙ x  ≈⟨ ∙-cong (sym a≈y) refl ⟩
              a ∙ x  ≈⟨ sym b≈a∙x ⟩
              b
            ∎

      total : Total _⊴ᴿ_
      total x y with selective x y
      ... | inj₁ ≈x = inj₂ (x , (trans (sym ≈x) (comm _ _)))
      ... | inj₂ ≈y = inj₁ (y , (sym ≈y))
