module Exercises where

  -- A lattice is an algebraic structure, (L, ∧, ∨) where ∧ and ∨ are binary
  -- operation on L, satisfying the following properties:
  --
  --   * ∧ and ∨ are commutative
  --   * ∧ and ∨ are associative
  --   * a ∨ (a ∧ b) ≡ a and a ∧ (a ∨ b) ≡ a (absorption)

  -- Capture the definition of an algebraic lattice.  Use the following
  -- module from the standard library.

  open import Algebra.FunctionProperties

  -- Show that in any lattice both ∧ and ∨ are idempotent.  Use the Agda
  -- standard library's equational reasoning toolkit to do this:

  open import Relation.Binary.PropositionalEquality

  -- Here's a demonstration of it in use:

  module EqReasoningExample where

    open import Function

    open import Data.Nat
    open import Data.Nat.Properties.Simple

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
