module Dijkstra.Algebra.Structures where

import Dijkstra.Algebra.FunctionProperties as FunctionProperties

open import Algebra.Structures
open import Data.Product
open import Data.Sum
open import Function
open import Level using (_⊔_)
open import Relation.Binary

open import Algebra.FunctionProperties using (Op₁; Op₂)

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
