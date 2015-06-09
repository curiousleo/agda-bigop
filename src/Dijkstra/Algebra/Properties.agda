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

  _⊴_ = leftCanonicalOrder _≈_ _+_

  +-idempotent : Idempotent _+_
  +-idempotent x with +-selective x x
  ... | inj₁ eq = eq
  ... | inj₂ eq = eq

--  equivalent : ∀ a b → a + b ≈ b → a ⊴ b
--  equivalent a b a+b≈b = b , (sym a+b≈b)

  isRightIncreasing : ∀ a b → a ⊴ (a * b)
  isRightIncreasing a b = a , trans (sym (+-absorbs-* a b)) (+-comm _ _)

module RequiresCommutativeMonoid
       {c ℓ} (cmon : CommutativeMonoid c ℓ) where

  open CommutativeMonoid cmon
  open FunctionProperties _≈_

  _⊴_ = rightCanonicalOrder _≈_ _∙_

  isTotalOrder : Selective _∙_ → IsTotalOrder _≈_ (rightCanonicalOrder _≈_ _∙_)
  isTotalOrder selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴-reflexive
              ; trans = ⊴-transitive
              }
          ; antisym = ⊴-antisym
          }
      ; total = total
    }
    where
      ⊴-reflexive : _≈_ ⇒ _⊴_
      ⊴-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity a) a≈b)

      ⊴-transitive : Transitive _⊴_
      ⊴-transitive {a} {b} {c} (x , b≈a∙x) (y , c≈b∙y) =
        x ∙ y , trans c≈b∙y (trans (∙-cong b≈a∙x refl) (assoc _ _ _))

      ⊴-antisym : Antisymmetric _≈_ _⊴_
      ⊴-antisym {a} {b} (x , b≈a∙x) (y , a≈b∙y) with selective a x | selective b y
      ... | _          | inj₁ b∙y≈b = trans a≈b∙y b∙y≈b
      ... | inj₁ a∙x≈a | _          = sym (trans b≈a∙x a∙x≈a)
      ... | inj₂ a∙x≈x | inj₂ b∙y≈y = eq
        where
          open import Relation.Binary.EqReasoning setoid

          a≈y = trans a≈b∙y b∙y≈y
          b≈x = trans b≈a∙x a∙x≈x

          eq : a ≈ b
          eq = begin
            a      ≈⟨ a≈y ⟩
            y      ≈⟨ sym b∙y≈y ⟩
            b ∙ y  ≈⟨ ∙-cong b≈x refl ⟩
            x ∙ y  ≈⟨ comm _ _ ⟩
            y ∙ x  ≈⟨ ∙-cong (sym a≈y) refl ⟩
            a ∙ x  ≈⟨ sym b≈a∙x ⟩
            b      ∎

      total : Total _⊴_
      total x y with selective x y
      ... | inj₁ ≈x = inj₂ (x , (trans (sym ≈x) (comm _ _)))
      ... | inj₂ ≈y = inj₁ (y , (sym ≈y))
