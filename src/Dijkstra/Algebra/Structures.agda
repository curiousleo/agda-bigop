module Dijkstra.Algebra.Structures where

open import Algebra.Structures
open import Data.Product
open import Data.Sum
open import Function
open import Level using (_⊔_)
open import Relation.Binary

open import Algebra.FunctionProperties as FunctionProperties
  using (Op₁; Op₂)
import Algebra.MoreFunctionProperties as MoreFunctionProperties

record IsDijkstraAlgebra {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                         (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  open MoreFunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    +-selective           : Selective +
    +-zero                : Zero 1# +

    *-identityˡ           : LeftIdentity 1# *
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
