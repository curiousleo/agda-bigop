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
  ⊕-associative (x ∷ xs) ys zs
    rewrite
      ⊕-associative xs ys zs = refl

  map-⊕ : ∀ {A B} → (f : A → B) → ∀ xs ys → map f (xs ⊕ ys) ≡ map f xs ⊕ map f ys
  map-⊕ f []       ys = refl
  map-⊕ f (x ∷ xs) ys
    rewrite
      map-⊕ f xs ys = refl

  reverse-⊕ : ∀ {A} → (xs ys : List A) → reverse (xs ⊕ ys) ≡ (reverse ys) ⊕ (reverse xs)
  reverse-⊕ []       ys = sym (⊕-[] (reverse ys))
  reverse-⊕ (x ∷ xs) ys
    rewrite reverse-⊕ xs ys = sym (⊕-associative (reverse ys) (reverse xs) (x ∷ []))

  reverse-reverse : ∀ {A} → (xs : List A) → reverse (reverse xs) ≡ xs
  reverse-reverse []       = refl
  reverse-reverse (x ∷ xs) = trans (reverse-⊕ (reverse xs) (x ∷ [])) {!!} -- rewrite??

  module Vectors where

    -- A in the data type below is a parameter, whereas : ℕ → Set states that there
    -- is a single natural number index for the data type.  Parameters stay constant
    -- during pattern matching, whereas indices vary, and provide information for the
    -- type checker to use.  They're used to express invariants in inductive data types,
    -- like the following type of length-indexed lists, or vectors:
    data Vec (A : Set) : ℕ → Set where
      []  : Vec A 0
      _∷_ : ∀ {m} → A → Vec A m → Vec A (suc m)

    -- Fill in the following.  Note the types provide more information, and
    -- dispense with the need to prove properties about the preservation of
    -- lengths like we needed to do with lists:

    _⊕′_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
    []       ⊕′ ys = ys
    (x ∷ xs) ⊕′ ys = x ∷ (xs ⊕′ ys)

    map′ : ∀ {A B m} → (f : A → B) → Vec A m → Vec B m
    map′ f []       = []
    map′ f (x ∷ xs) = f x ∷ map′ f xs

    suc₀ : (m : ℕ) → m + suc 0 ≡ suc m
    suc₀ zero = refl
    suc₀ (suc m) = cong suc (suc₀ m)

    reverse′ : ∀ {A m} → Vec A m → Vec A m
    reverse′ [] = []
--    reverse′ (x ∷ xs) = (reverse′ xs) ⊕′ (x ∷ [])
    reverse′ {m = suc n} (x ∷ xs)
      rewrite sym (suc₀ n) = (reverse′ xs) ⊕′ (x ∷ [])
