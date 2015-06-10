module Dijkstra.Algebra.Model where

open import Dijkstra.Algebra

open import Algebra.Structures
open import Data.Product
open import Function

module NatProperties where

  open import Relation.Binary.PropositionalEquality using (_≡_; cong)

  open import Data.Nat
  open import Data.Nat.Properties.Simple
  open import Data.Nat.Properties using (⊔-⊓-0-isCommutativeSemiringWithoutOne)
  open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne
    renaming ( *-assoc to ⊓-assoc
             ; *-comm to ⊓-comm
             )
    public
  open import Data.Sum

  open import Dijkstra.Algebra.FunctionProperties (_≡_ {A = ℕ})

  ⊓-selective : Selective _⊓_
  ⊓-selective zero    n = inj₁ refl
  ⊓-selective (suc m) zero    = inj₂ refl
  ⊓-selective (suc m) (suc n) with ⊓-selective m n
  ... | inj₁ p rewrite p = inj₁ refl
  ... | inj₂ p rewrite p = inj₂ refl

  ⊓-idempotent : Idempotent _⊓_
  ⊓-idempotent m with ⊓-selective m m
  ... | inj₁ p = p
  ... | inj₂ p = p

  ⊓-absorbs-+ : _⊓_ Absorbs _+_
  ⊓-absorbs-+ zero    n = refl
  ⊓-absorbs-+ (suc m) zero rewrite +-right-identity m = cong ℕ.suc $ ⊓-idempotent m
  ⊓-absorbs-+ (suc m) (suc n) = cong ℕ.suc $ ⊓-absorbs-+ m (ℕ.suc n)

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
                                                       { +-isCommutativeMonoid = record { isSemigroup = record { isEquivalence = isEquivalence ; assoc = assoc ; ∙-cong = cong₂ min } ; identityˡ = identityˡ ; comm = comm }
                                                       ; +-selective = min-selective
                                                       ; +-zero = +-zero
                                                       ; *-identity = *-identity
                                                       ; *-cong = cong₂ _+_
                                                       ; +-absorbs-* = +-absorbs-*
                                                       }
                               }
