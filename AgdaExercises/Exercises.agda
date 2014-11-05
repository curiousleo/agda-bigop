module Exercises where

  -- Empty type, or logical false
  data ⊥ : Set where

  -- Elimination rule for the empty type, or the logical principle of
  -- ex falso quod libet.
  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  -- Unit type, or logical truth
  data ⊤ : Set where
    tt : ⊤

  -- Negation of a type
  ¬_ : Set → Set
  ¬ A = A → ⊥

  -- Union type, or logical disjunction
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  -- Elimination rule for logical disjunction:
  ⊎-elim : {A B C : Set} → (A ⊎ B) → (A → C) → (B → C) → C
  ⊎-elim (inl x) left right = left x
  ⊎-elim (inr x) left right = right x

  -- Non-dependent Cartesian product type, or logical conjunction
  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  -- Two elimination rules for conjunction:
  ×-elim₁ : {A B : Set} → A × B → A
  ×-elim₁ (a , b) = a

  ×-elim₂ : {A B : Set} → A × B → B
  ×-elim₂ (a , b) = b

  -- The identity (equality) type
  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

  -- Symmetry of equality:
  sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  -- Transitivity of equality:
  trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl

  -- Congruence, which allows us to transport an equality under a function symbol
  cong : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
  cong f refl = refl

  -- The type of natural numbers:
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  -- constructors are injective in Agda, but you must do the proof by hand:
  succ-injective : (m n : ℕ) → succ m ≡ succ n → m ≡ n
  succ-injective zero     (succ n)  ()
  succ-injective (succ m) zero      ()
  succ-injective zero     zero      refl = refl
  succ-injective (succ m) (succ .m) refl = refl

  -- addition:
  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  succ m + n = succ (m + n)

  -- show: addition is commutative, associative and zero is a right identity for addition below
  +-right-id : (m : ℕ) → (m + zero) ≡ m
  +-right-id zero     = refl
  +-right-id (succ x) = cong succ (+-right-id x)

  +-comm : (m n : ℕ) → (m + n) ≡ (n + m)
  +-comm zero     zero     = refl
  +-comm zero     (succ n) = cong succ (sym (+-right-id n))
  +-comm (succ m) zero     = cong succ (+-right-id m)
  +-comm (succ m) (succ n) = cong succ (trans (lemma m n) (+-comm (succ m) n)) where
    lemma : (p q : ℕ) → (p + succ q) ≡ succ (p + q)
    lemma zero q = refl
    lemma (succ p) q = cong succ (trans (lemma p q) refl)

  +-assoc : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
  +-assoc zero     n p = refl
  +-assoc (succ m) n p = cong succ (+-assoc m n p)
