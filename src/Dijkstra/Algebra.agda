module Dijkstra.Algebra where

open import Dijkstra.Algebra.Structures

open import Algebra public
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Product
open import Function
open import Level
open import Relation.Binary

-- rightCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
-- rightCanonicalOrder _≈_ _∙_ a b = ∃ λ c → b ≈ (a ∙ c)

record DijkstraAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    0#                : Carrier
    1#                : Carrier
    isDijkstraAlgebra : IsDijkstraAlgebra _≈_ _+_ _*_ 0# 1#

  open IsDijkstraAlgebra isDijkstraAlgebra public

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∙_ = _+_
      ; ε = 0#
      ; isCommutativeMonoid = +-isCommutativeMonoid
      }

  _⊴_ : Rel Carrier _
  a ⊴ b = ∃ λ c → b ≈ (a + c) -- rightCanonicalOrder _≈_ _+_

record Prebimonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    0#             : Carrier
    1#             : Carrier
    isPrebimonoid  : IsPrebimonoid _≈_ _+_ _*_ 0# 1#

  open IsPrebimonoid isPrebimonoid public

  *-commutativeMonoid : CommutativeMonoid _ _
  *-commutativeMonoid =
    record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∙_ = _*_
      ; ε = 0#
      ; isCommutativeMonoid = *-isCommutativeMonoid
      }

record Bimonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ
    _+_         : Op₂ Carrier
    _*_         : Op₂ Carrier
    0#          : Carrier
    1#          : Carrier
    isBimonoid  : IsBimonoid _≈_ _+_ _*_ 0# 1#

  open IsBimonoid isBimonoid public

  *-commutativeMonoid : CommutativeMonoid _ _
  *-commutativeMonoid =
    record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∙_ = _*_
      ; ε = 0#
      ; isCommutativeMonoid = *-isCommutativeMonoid
      }

  _⊴_ = rightCanonicalOrder _≈_ _+_
