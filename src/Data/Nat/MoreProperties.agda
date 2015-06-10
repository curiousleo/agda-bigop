module Data.Nat.MoreProperties where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Sum

open import Function

open import Relation.Binary.PropositionalEquality

open import Algebra.FunctionProperties (_≡_ {A = ℕ})
open import Algebra.MoreFunctionProperties (_≡_ {A = ℕ})

⊓-comm : Commutative _⊓_
⊓-comm zero    zero    = refl
⊓-comm zero    (suc n) = refl
⊓-comm (suc m) zero    = refl
⊓-comm (suc m) (suc n) = cong ℕ.suc $ ⊓-comm m n

⊓-assoc : Associative _⊓_
⊓-assoc zero    n       o       = refl
⊓-assoc (suc m) zero    o       = refl
⊓-assoc (suc m) (suc n) zero    = refl
⊓-assoc (suc m) (suc n) (suc o) = cong ℕ.suc $ ⊓-assoc m n o

⊓-selective : Selective _⊓_
⊓-selective zero    n       = inj₁ refl
⊓-selective (suc m) zero    = inj₂ refl
⊓-selective (suc m) (suc n) with ⊓-selective m n
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p rewrite p = inj₂ refl

⊓-idempotent : Idempotent _⊓_
⊓-idempotent m with ⊓-selective m m
... | inj₁ p = p
... | inj₂ p = p

⊓-absorbs-+ : _⊓_ Absorbs _+_
⊓-absorbs-+ zero    n        = refl
⊓-absorbs-+ (suc m) zero
  rewrite +-right-identity m = cong suc $ ⊓-idempotent m
⊓-absorbs-+ (suc m) (suc n)  = cong suc $ ⊓-absorbs-+ m (suc n)
