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

  -- Agda has nested modules, everything above is in the scope of the body
  -- of the following module, but everything within this module body is not
  -- in scope outside the module unless it is specifically opened, or referred
  -- to using a qualified name, e.g. Nested.foo
  module Nested where

    -- More on logic in Agda.  So far we have:
    --   * ⊥ is the type representing false
    --   * ⊤ is the type representing true
    --   * _⊎_ is the type representing logical disjunction
    --   * _×_ is the type representing logical conjunction
    --
    -- Which leaves universal and existential quantification:
    --  * The dependent function space (x : A) → … represents universal
    --    quantification.  The type (x : A) → … may either be read as
    --    a function type, or alternatively as something akin to
    --      ∀x : A. …
    --  * Existential quantification is more complicated.  As Agda is
    --    constructive to solve a goal of the form ∃ x . P x we must
    --    construct by hand a witness x satisfying P.  Contrast this
    --    with classical logic where we may also solve an existential
    --    goal by showing that it is impossible for such an x not to
    --    exist.  We therefore must model existentials as dependent
    --    pairs (i.e. a generalisation of _×_).  We can therefore dispense
    --    with _×_ altogether, using it merely as a simplified form of
    --    a dependent pair.

    -- Dependent pairs:
    record Σ (A : Set) (P : A → Set) : Set where
      constructor
        _,_
      field
        proj₁ : A
        proj₂ : P proj₁

    -- Cartesian product type (non-dependent product):
    _×′_ : Set → Set → Set
    A ×′ B = Σ A (λ x → B)

    -- Σ A (λ x → B) should be read as ∃(x : A). B

    -- Show again:
    ×′-elim₁ : {A B : Set} → A ×′ B → A
    ×′-elim₁ = {!!}

    -- Define lists:

    data List (A : Set) : Set where
      []  : List A
      _∷_ : A → List A → List A

    -- Show the following (trivial) fact :
    exists-subcomponent : {A : Set} → (y : A) → (xs ys : List A) → xs ≡ (y ∷ ys) → Σ A (λ x → xs ≡ (x ∷ ys))
    exists-subcomponent = {!!}

    -- Define length:
    length : {A : Set} → List A → ℕ
    length = {!!}

    -- Define map:
    map : {A B : Set} → (f : A → B) → List A → List B
    map f xs = {!!}

    -- Define append:
    _⊕_ : {A : Set} → List A → List A → List A
    xs ⊕ ys = {!!}

    -- Define reverse using append:
    reverse : {A : Set} → List A → List A
    reverse = {!!}

    -- Show the following facts (may need additional lemmas, or perhaps reordering):

    []-⊕ : {A : Set} → (xs : List A) → (xs ⊕ []) ≡ xs
    []-⊕ = {!!}

    reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
    reverse-reverse = {!!}

    length-reverse : {A : Set} → (xs : List A) → length (reverse xs) ≡ length xs
    length-reverse = {!!}

    length-⊕ : {A : Set} → (xs ys : List A) → length (xs ⊕ ys) ≡ (length xs + length ys)
    length-⊕ = {!!}

    length-map : {A B : Set} → (f : A → B) → (xs : List A) → length (map f xs) ≡ length xs
    length-map = {!!}

    -- Note how []-⊕ and +-right-id are similar.  [] is the equivalent of zero and _⊕_ is
    -- the equivalent of _+_, with the two lemmas both showing the `zero' element is a
    -- right neutral for the `+` element.  This suggests we can do some factoring with
    -- a type-level function:

    IsRightNeutral : {A : Set} → (ε : A) → (_⊕_ : A → A → A) → Set
    IsRightNeutral {A} ε _⊕_ = (xs : A) → (xs ⊕ ε) ≡ xs

    -- Now use IsRightNeutral to reformulate both +-right-id and []-⊕:

    +-right-id′ : IsRightNeutral zero _+_
    +-right-id′ = {!!}

    -- Remove the `{A : Set} →' to see what happens below.  Why does that happen?
    []-⊕′ : {A : Set} → IsRightNeutral {A = List A} [] _⊕_
    []-⊕′ = {!!}

    -- In fact both the naturals and lists are monoids:

    -- This record contains proofs of what it means to be monoidal:
    record IsMonoid {A : Set} (_⋆_ : A → A → A) (ε : A) : Set where
      field
        right-neutral : IsRightNeutral ε _⋆_
        -- fill in left neutral field here, you will need to define another
        -- type level function to capture what it means to be a left neutral

    -- This record bundles up a type and some operations, along with proofs
    -- that those operations form a monoid.  Note that the type of Monoid is
    -- Set₁.  Try to change Set₁ to Set and try to guess what is going wrong.
    record Monoid : Set₁ where
      field
        Carrier   : Set
        _⋆_       : Carrier → Carrier → Carrier
        ε         : Carrier
        is-monoid : IsMonoid _⋆_ ε

      -- We open is-monoid in this record so that all the proof
      -- in that record are then accessible in this record too
      open IsMonoid is-monoid public

    -- show that ℕ and lists are monoids:

    ℕ-monoid : Monoid
    ℕ-monoid = {!!}

    List-monoid : Monoid
    List-monoid = {!!}

    -- Now we can write some generic functions over monoids.  The obvious
    -- one is a monoidal fold.  Try to fill this in:

    fold : (m : Monoid) → List (Monoid.Carrier m) → Monoid.Carrier m
    fold = {!!}
