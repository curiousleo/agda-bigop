module Exercises where

  -- A lattice is an algebraic structure, (L, ∧, ∨) where ∧ and ∨ are binary
  -- operation on L, satisfying the following properties:
  --
  --   * ∧ and ∨ are commutative
  --   * ∧ and ∨ are associative
  --   * a ∨ (a ∧ b) ≡ a and a ∧ (a ∨ b) ≡ a (absorption)

  -- Capture the definition of an algebraic lattice.  Use the following
  -- module from the standard library.

  import Algebra.FunctionProperties as FunctionProperties
  open FunctionProperties using (Op₂)
  
  import Level
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  -- inspired by Algebra.agda ...
  record IsLattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                   (∧ ∨ : Op₂ A) : Set (a Level.⊔ ℓ) where
    open FunctionProperties ≈
    field
      ∧-is-commutative : Commutative ∧
      ∨-is-commutative : Commutative ∨
      ∧-is-associative : Associative ∧
      ∨-is-associative : Associative ∨
      is-absorptive    : Absorptive ∧ ∨

  -- why doesn't this work?
  -- record IsLattice {ℓ} {A : Set ℓ}
  --                  (∧ ∨ : Op₂ A) : Set (Level.suc ℓ) where
  --   field
  --     ∧-is-commutative : Commutative ∧
  --     ∨-is-commutative : Commutative ∨
  --     ∧-is-associative : Associative ∧
  --     ∨-is-associative : Associative ∨
  --     is-absorptive    : Absorptive ∧ ∨

  record Lattice {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
    field
      Carrier    : Set ℓ
      -- _≈_        : Rel Carrier ℓ
      _∧_        : Op₂ Carrier
      _∨_        : Op₂ Carrier
      -- is-lattice : IsLattice _≈_ _∧_ _∨_
      is-lattice : IsLattice _≡_ _∧_ _∨_

    open IsLattice is-lattice public

  -- Show that in any lattice both ∧ and ∨ are idempotent.  Use the Agda
  -- standard library's equational reasoning toolkit to do this:

  open import Relation.Binary.PropositionalEquality

  module DerivedLatticeProperties {ℓ ℓ′} (l : Lattice {ℓ} {ℓ′}) where
    open Lattice l

    open import Data.Product
    open FunctionProperties

    ∧-is-idempotent : Idempotent _≡_ _∧_
    ∧-is-idempotent x =
      begin
        x ∧ x
          ≡⟨ cong (_∧_ x) (sym (proj₂ is-absorptive x x)) ⟩
        x ∧ (x ∨ (x ∧ x))
          ≡⟨ proj₁ is-absorptive x (x ∧ x) ⟩
        x
      ∎
      where
        open ≡-Reasoning

    ∨-is-idempotent : Idempotent _≡_ _∨_
    ∨-is-idempotent x =
      begin
        x ∨ x
          ≡⟨ cong (_∨_ x) (sym (proj₁ is-absorptive x x)) ⟩
        x ∨ (x ∧ (x ∨ x))
          ≡⟨ proj₂ is-absorptive x (x ∨ x) ⟩
        x
      ∎
      where
        open ≡-Reasoning

  module EqReasoningExample where

    open import Function

    open import Data.Nat
    open import Data.Nat.Properties.Simple

    open import Algebra.FunctionProperties

    +-commutative : Commutative _≡_ _+_
    +-commutative zero    n = sym ∘ +-right-identity $ n
    +-commutative (suc m) n =
      begin
        suc (m + n)
          ≡⟨ cong suc (+-commutative m n) ⟩
        suc (n + m)
          ≡⟨ sym (+-suc n m) ⟩
        n + suc m
      ∎
      where
        open ≡-Reasoning
