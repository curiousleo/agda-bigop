module Dijkstra.Algebra where

open import Dijkstra.Algebra.Structures

open import Algebra public
open import Algebra.FunctionProperties
  using (Op₂)
open import Algebra.Structures
open import Data.Product
open import Function
open import Level
open import Relation.Binary


record DijkstraAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _≟_              : Decidable _≈_
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    0#                : Carrier
    1#                : Carrier
    isDijkstraAlgebra : IsDijkstraAlgebra _≈_ _+_ _*_ 0# 1#

  open IsDijkstraAlgebra isDijkstraAlgebra public

  decSetoid : DecSetoid c ℓ
  decSetoid =
    record
      { Carrier          = Carrier
      ; _≈_              = _≈_
      ; isDecEquivalence =
          record { isEquivalence = isEquivalence ; _≟_ = _≟_ }
      }

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∙_ = _+_
      ; ε = 0#
      ; isCommutativeMonoid = +-isCommutativeMonoid
      }

  open CommutativeMonoid +-commutativeMonoid
    using (setoid)
    renaming (monoid to +-monoid) public
