module Exercises where

  open import Data.Nat

  -- Import the equality type, and related functionality
  open import Relation.Binary.PropositionalEquality hiding ([_])

  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  -- ∀ {A} is equivalent to {A : Set}.  ∀ A is equivalent to (A : Set)
  [_] : ∀ {A} → A → List A
  [ e ] = e ∷ []

  length : ∀ {A} → List A → ℕ
  length []       = 0
  length (x ∷ xs) = suc (length xs)

  map : ∀ {A B} → (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  _⊕_ : ∀ {A} → List A → List A → List A
  []       ⊕ ys = ys
  (x ∷ xs) ⊕ ys = x ∷ (xs ⊕ ys)

  reverse : ∀ {A} → List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ⊕ [ x ]

  ⊕-[] : ∀ {A} → (xs : List A) → xs ⊕ [] ≡ xs
  ⊕-[] []       = refl
  ⊕-[] (x ∷ xs)
    -- Use rewrite with a term of equality type to replace one side of the equality
    -- with the other.
    rewrite
      ⊕-[] xs = refl

  -- Use rewrite to solve the following:

  ⊕-associative : ∀ {A} → (xs ys zs : List A) → xs ⊕ (ys ⊕ zs) ≡ (xs ⊕ ys) ⊕ zs
  ⊕-associative []       ys zs = refl
  ⊕-associative (x ∷ xs) ys zs = {!!}

  map-⊕ : ∀ {A B} → (f : A → B) → ∀ xs ys → map f (xs ⊕ ys) ≡ map f xs ⊕ map f ys
  map-⊕ f []       ys = refl
  map-⊕ f (x ∷ xs) ys = {!!}

  reverse-⊕ : ∀ {A} → (xs ys : List A) → reverse (xs ⊕ ys) ≡ reverse ys ⊕ reverse xs
  reverse-⊕ []       ys = {!!}
  reverse-⊕ (x ∷ xs) ys = {!!}

  reverse-reverse : ∀ {A} → (xs : List A) → reverse (reverse xs) ≡ xs
  reverse-reverse []       = refl
  reverse-reverse (x ∷ xs) = {!!}

  
