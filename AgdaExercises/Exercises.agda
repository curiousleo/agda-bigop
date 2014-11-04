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
  ⊎-elim union left right = {!!}

  -- Non-dependent Cartesian product type, or logical conjunction
  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  -- Two elimination rules for conjunction:
  ×-elim₁ : {A B : Set} → A × B → A
  ×-elim₁ prod = {!!}

  ×-elim₂ : {A B : Set} → A × B → B
  ×-elim₂ prod = {!!}

  -- The identity (equality) type
  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

  -- Symmetry of equality:
  sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
  sym = {!!}

  -- Transitivity of equality:
  trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans = {!!}

  -- Congruence, which allows us to transport an equality under a function symbol
  cong : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
  cong = {!!}

  -- The type of natural numbers:
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  -- constructors are injective in Agda, but you must do the proof by hand:
  succ-injective : (m n : ℕ) → succ m ≡ succ n → m ≡ n
  succ-injective = {!!}

  -- addition:
  _+_ : ℕ → ℕ → ℕ
  m + n = {!!}

  -- show: addition is commutative, associative and zero is a right identity for addition below

  
  
