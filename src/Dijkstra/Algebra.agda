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

module NatProperties where

  open import Relation.Binary.PropositionalEquality

  open import Data.Nat
  open import Data.Nat.Properties.Simple
  open import Data.Sum

  open import Dijkstra.Algebra.FunctionProperties (_≡_ {A = ℕ})

  ⊓-selective : Selective _⊓_
  ⊓-selective ℕ.zero    n = inj₁ refl
  ⊓-selective (ℕ.suc m) ℕ.zero    = inj₂ refl
  ⊓-selective (ℕ.suc m) (ℕ.suc n) with ⊓-selective m n
  ... | inj₁ p rewrite p = inj₁ refl
  ... | inj₂ p rewrite p = inj₂ refl

  ⊓-idempotent : Idempotent _⊓_
  ⊓-idempotent m with ⊓-selective m m
  ... | inj₁ p = p
  ... | inj₂ p = p

  ⊓-comm : Commutative _⊓_
  ⊓-comm zero zero    = refl
  ⊓-comm zero (suc n) = refl
  ⊓-comm (suc m) zero = refl
  ⊓-comm (suc m) (suc n) = cong ℕ.suc $ ⊓-comm m n

  ⊓-assoc : Associative _⊓_
  ⊓-assoc ℕ.zero    n o = refl
  ⊓-assoc (ℕ.suc m) ℕ.zero o = refl
  ⊓-assoc (ℕ.suc m) (ℕ.suc n) ℕ.zero = refl
  ⊓-assoc (ℕ.suc m) (ℕ.suc n) (ℕ.suc o) = cong ℕ.suc $ ⊓-assoc m n o

  ⊓-absorbs-+ : _⊓_ Absorbs _+_
  ⊓-absorbs-+ zero    n = refl
  ⊓-absorbs-+ (ℕ.suc m) ℕ.zero rewrite +-right-identity m = cong ℕ.suc $ ⊓-idempotent m
  ⊓-absorbs-+ (ℕ.suc m) (ℕ.suc n) = cong ℕ.suc $ ⊓-absorbs-+ m (ℕ.suc n)

module Foo where

  open import Relation.Binary.PropositionalEquality

  open import Data.Nat as Nat
    renaming (_+_ to _+′_; _*_ to _*′_)
  open import Data.Sum

  data ℕ∞ : Set where
    ↑ : ℕ → ℕ∞
    ∞ : ℕ∞

  open import Dijkstra.Algebra.FunctionProperties (_≡_ {A = ℕ∞})

  min : ℕ∞ → ℕ∞ → ℕ∞
  min (↑ m) (↑ n) = ↑ (m ⊓ n)
  min (↑ m) ∞     = ↑ m
  min ∞     (↑ n) = ↑ n
  min ∞     ∞     = ∞

  _+_ : ℕ∞ → ℕ∞ → ℕ∞
  ↑ m + ↑ n = ↑ (m +′ n)
  ↑ m + ∞   = ∞
  ∞   + n   = ∞

  +-zeroˡ : LeftZero (↑ 0) min
  +-zeroˡ (↑ m) = refl
  +-zeroˡ ∞     = refl

  +-zeroʳ : RightZero (↑ 0) min
  +-zeroʳ (↑  ℕ.zero)   = refl
  +-zeroʳ (↑ (ℕ.suc m)) = refl
  +-zeroʳ ∞             = refl

  +-zero : Zero (↑ 0) min
  +-zero = +-zeroˡ , +-zeroʳ

  *-identity : LeftIdentity (↑ 0) _+_
  *-identity (↑ m) = refl
  *-identity ∞     = refl

  min-selective : Selective min
  min-selective (↑ m) (↑ n) with NatProperties.⊓-selective m n
  ... | inj₁ p rewrite p = inj₁ refl
  ... | inj₂ p rewrite p = inj₂ refl
  min-selective (↑ m) ∞     = inj₁ refl
  min-selective ∞     (↑ n) = inj₂ refl
  min-selective ∞     ∞     = inj₁ refl

  identityˡ : LeftIdentity ∞ min
  identityˡ (↑ m) = refl
  identityˡ ∞     = refl

  comm : Commutative min
  comm (↑ m) (↑ n) rewrite NatProperties.⊓-comm m n = refl
  comm (↑ m) ∞ = refl
  comm ∞ (↑ n) = refl
  comm ∞ ∞ = refl

  assoc : Associative min
  assoc (↑ m) (↑ n) (↑ o) rewrite NatProperties.⊓-assoc m n o = refl
  assoc (↑ m) (↑ n) ∞ = refl
  assoc (↑ m) ∞ (↑ o) = refl
  assoc (↑ m) ∞ ∞ = refl
  assoc ∞ (↑ n) (↑ o) = refl
  assoc ∞ (↑ n) ∞ = refl
  assoc ∞ ∞ (↑ o) = refl
  assoc ∞ ∞ ∞ = refl

  +-absorbs-* : min Absorbs _+_
  +-absorbs-* (↑ m) (↑ n) rewrite NatProperties.⊓-absorbs-+ m n = refl
  +-absorbs-* (↑ m) ∞    = refl
  +-absorbs-* ∞    (↑ n) = refl
  +-absorbs-* ∞    ∞     = refl

  example-dijkstra-algebra : DijkstraAlgebra _ _
  example-dijkstra-algebra = record
                               { Carrier = ℕ∞
                               ; _≈_ = _≡_
                               ; _+_ = min
                               ; _*_ = _+_
                               ; 0# = ∞
                               ; 1# = ↑ 0
                               ; isDijkstraAlgebra = record
                                                       { +-isCommutativeMonoid = record { isSemigroup = record { isEquivalence = isEquivalence ; assoc = assoc ; ∙-cong = {!!} } ; identityˡ = identityˡ ; comm = comm }
                                                       ; +-selective = min-selective
                                                       ; +-zero = +-zero
                                                       ; *-identity = *-identity
                                                       ; *-cong = {!!}
                                                       ; +-absorbs-* = +-absorbs-*
                                                       }
                               }

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
