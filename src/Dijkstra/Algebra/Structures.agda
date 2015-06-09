module Dijkstra.Algebra.Structures where

import Dijkstra.Algebra.FunctionProperties as FunctionProperties

open import Algebra.Structures
open import Data.Product
open import Data.Sum
open import Function
open import Level using (_⊔_)
open import Relation.Binary

open import Algebra.FunctionProperties using (Op₁; Op₂)

rightCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
rightCanonicalOrder _≈_ _∙_ a b = ∃ λ c → b ≈ (a ∙ c)

record IsDijkstraAlgebra {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                         (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    +-selective           : Selective +
    +-zero                : Zero 1# +

    *-identity            : LeftIdentity 1# *
    *-cong                : * Preserves₂ ≈ ⟶ ≈ ⟶ ≈

    +-absorbs-*           : + Absorbs *

  open IsCommutativeMonoid +-isCommutativeMonoid public
         hiding (identityˡ)
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )

  isTotalOrder : IsTotalOrder ≈ (rightCanonicalOrder ≈ +)
  isTotalOrder =
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
      ; total = total }
    where
      _⊴_ = rightCanonicalOrder ≈ +

      ⊴-reflexive : ≈ ⇒ _⊴_
      ⊴-reflexive {a} {b} a≈b = 0# , sym (trans (proj₂ +-identity a) a≈b)

      ⊴-transitive : Transitive _⊴_
      ⊴-transitive {a} {b} {c} (x , b≈a+x) (y , c≈b+y) =
        + x y , trans c≈b+y (trans (+-cong b≈a+x refl) (+-assoc _ _ _))

      ⊴-antisym : Antisymmetric ≈ _⊴_
      ⊴-antisym {a} {b} (x , b≈a+x) (y , a≈b+y) with +-selective a x | +-selective b y
      ... | _          | inj₁ b+y≈b = trans a≈b+y b+y≈b
      ... | inj₁ a+x≈a | _          = sym (trans b≈a+x a+x≈a)
      ... | inj₂ a+x≈x | inj₂ b+y≈y = eq
        where
          setoid = record { Carrier = A ; _≈_ = ≈ ; isEquivalence = isEquivalence }
          open import Relation.Binary.EqReasoning setoid

          a≈y = trans a≈b+y b+y≈y
          b≈x = trans b≈a+x a+x≈x

          eq : ≈ a b
          eq = begin
            a      ≈⟨ a≈y ⟩
            y      ≈⟨ sym b+y≈y ⟩
            + b y  ≈⟨ +-cong b≈x refl ⟩
            + x y  ≈⟨ +-comm _ _ ⟩
            + y x  ≈⟨ +-cong (sym a≈y) refl ⟩
            + a x  ≈⟨ sym b≈a+x ⟩
            b      ∎

      total : Total _⊴_
      total x y with +-selective x y
      ... | inj₁ ≈x = inj₂ (x , (trans (sym ≈x) (+-comm _ _)))
      ... | inj₂ ≈y = inj₁ (y , (sym ≈y))

record IsSelectiveMonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                         (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isMonoid  : IsMonoid ≈ ∙ ε
    selective : Selective ∙

  open IsMonoid isMonoid public

{-
record IsSemilattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                     (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isCommutativeMonoid : IsCommutativeMonoid ≈ ∙ ε
    selective           : Selective ∙

  open IsCommutativeMonoid isCommutativeMonoid public
-}

record IsPrebimonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                     (+ : Op₂ A) (* : Op₂ A) (0# : A) (1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    *-isCommutativeMonoid : IsCommutativeMonoid ≈ * 0#
    +-cong                : + Preserves₂ ≈ ⟶ ≈ ⟶ ≈

  open IsCommutativeMonoid *-isCommutativeMonoid public
         hiding (identityˡ)
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  ; isMonoid    to *-isMonoid
                  ; comm        to *-comm
                  )

record IsBimonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                     (+ : Op₂ A) (* : Op₂ A) (0# : A) (1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isSemigroup         : IsSemigroup ≈ +
    *-isCommutativeMonoid : IsCommutativeMonoid ≈ * 0#

  open IsSemigroup +-isSemigroup public
         using ()
         renaming (assoc to +-assoc)

  open IsCommutativeMonoid *-isCommutativeMonoid public
         hiding (identityˡ)
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  ; isMonoid    to *-isMonoid
                  ; comm        to *-comm
                  )
