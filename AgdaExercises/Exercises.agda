module Exercises where

  open import Data.Nat hiding (fold)

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

  -- I would solve this like the lemma reverse-⊕′ below:
  reverse-⊕ : ∀ {A} → (xs ys : List A) → reverse (xs ⊕ ys) ≡ (reverse ys) ⊕ (reverse xs)
  reverse-⊕ []       ys = sym (⊕-[] (reverse ys))
  reverse-⊕ (x ∷ xs) ys
    rewrite reverse-⊕ xs ys = sym (⊕-associative (reverse ys) (reverse xs) (x ∷ []))

  -- My solution:
  reverse-⊕′ : ∀ {A} → (xs ys : List A) → reverse (xs ⊕ ys) ≡ (reverse ys) ⊕ (reverse xs)
  reverse-⊕′ []       ys
    rewrite ⊕-[] (reverse ys) = refl
  reverse-⊕′ (x ∷ xs) ys
    -- Note you chain together multiple rewrite steps by separating them with a bar: |
    rewrite
      reverse-⊕′ xs ys
    | ⊕-associative (reverse ys) (reverse xs) [ x ] = refl

  -- You almost never use trans.  This can be solved directly with rewriting.  Look at
  -- the IH (i.e. the recursive call to reverse-reverse xs) and its type, and also
  -- consider just rewriting with reverse-⊕ to push reverse through the append.  In fact,
  -- note what happens when you rewrite with reverse-⊕.  What happens to reverse [ x ]?
  -- It disappears, as reverse [ x ] is =β [ x ] (i.e. the two are definitionally equal).
  reverse-reverse : ∀ {A} → (xs : List A) → reverse (reverse xs) ≡ xs
  reverse-reverse []       = refl
  reverse-reverse (x ∷ xs)
    rewrite
      reverse-⊕ (reverse xs) [ x ]
    | reverse-reverse xs = refl

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

    -- Note this is an immediate corollary of two more primitive (and useful)
    -- lemmas: m + suc n ≡ suc (m + n) and m + zero ≡ zero.  Using these two
    -- lemmas you can just rewrite in reverse′ to close the obligations.
    suc₀ : (m : ℕ) → m + suc 0 ≡ suc m
    suc₀ zero = refl
    suc₀ (suc m) = cong suc (suc₀ m)

    reverse′ : ∀ {A m} → Vec A m → Vec A m
    reverse′ [] = []
--    reverse′ (x ∷ xs) = (reverse′ xs) ⊕′ (x ∷ [])
    reverse′ {m = suc n} (x ∷ xs)
      rewrite sym (suc₀ n) = (reverse′ xs) ⊕′ (x ∷ [])

  module Levels where

    -- Recall how we defined monoids in Agda, with a record.  The type of the
    -- Monoid record was Set₁, not the usual Set.  In fact, in Agda, there is an
    -- infinite universe hierarchy of Set₀, Set₁, Set₂, and so on and so forth.
    -- The familiar Set is identified with Set₀, the `universe of small types'.
    -- Set₀ has type Set₁, Set₁ has type Set₂, Set₂ has type Set₃, and so on.
    -- If instead we had Set₀ : Set₀, Agda would become inconsistent, as you
    -- would be able to encode Girard's paradox (related to the Burali-Forti and
    -- Russell's paradoxes) inside Agda, obtaining a contradiction, and hence
    -- being able to prove ⊥.  So, the hierarchy of universes exists to prevent
    -- this from happening, and there's various rules which dictate that types
    -- of functions spaces, records, and so on, when they mention Setᵢ for some i.

    -- For example:

    -- One must have type Set₁ because it has a field, Carrier, of type Set₀, and Set₀
    -- is `too small' to accomodate the type of this record:
    record One : Set₁ where
      field
        Carrier : Set₀

    -- Two must also have type Set₁ because it has a field, foo, of type Set₀ → Set₀,
    -- and Set₀ is `too small' to accommodate the type of this record:
    record Two : Set₁ where
      field
        foo : Set₀ → Set₀

    -- And so on.  If Agda notices a problem with universes, it will complain and produce
    -- an error.

    -- However, one problem with this system is that we now have multiple copies of
    -- Agda's internal logic, one at each universe level.  Recall:

    data ⊥ : Set₀ where

    -- Why must this be fixed at Set₀?  There is nothing wrong with:

    data ⊥′ : Set₁ where

    -- And in fact we can make an infinite number of copies of ⊥, ⊥ᵢ for each Setᵢ.
    -- This is really ugly.  But Agda provides a solution in allowing definitions,
    -- functions, records, data types, and so on to `float' across universe levels
    -- via `universe polymorphism'.  Consider the following:

    -- Agda's builtin type of universe levels and functions on then (middle-click
    -- the module name with your mouse in Emacs to open the module and inspect it):
    open import Level

    -- The empty type that is now free to `float' across universe levels ℓ:
    data Empty {ℓ} : Set ℓ where

    -- Fix a copy of Empty at Set₁:
    Empty₁ : Set₁
    Empty₁ = Empty

    -- Fix another copy of empty at Set₂.  Note how universes are correctly inferred
    -- based on usage.  Sometimes they may not be, in which case the term whose type
    -- is ambiguous is highlighted yellow, and you must help Agda out:
    Empty₂ : Set₂
    Empty₂ = Empty

    -- We provide another copy of record One, above.  Note how the record floats, but
    -- there is a fixed relationship between the record's type and the type of Carrier
    -- in that the record exists in the universe directly above Carrier.
    record Three {ℓ} : Set (Level.suc ℓ) where
      field
        Carrier : Set ℓ

    -- In fact, Three above does not have a fully general universe ascription.  This
    -- is more general:
    record Four {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
      field
        Carrier : Set ℓ

    -- Four allows us to have Carrier in Set₀, for instance, whilst Four itself lives
    -- in Set₄.  ℓ ⊔ ℓ′ should be read as the maximum of two universe levels, and
    -- suc bumps this up another level, to ensure Four's universe level is strictly
    -- greater than Carrier's.

    -- Universes affect everything in Agda, and for Agda code to be fully general you
    -- must include universe levels, allowing definitions and types to float, and try
    -- to assign the most general universe ascription as possible.  For example:

    data Nat′ {ℓ} : Set ℓ where
      zero′ : Nat′
      succ′ : Nat′ → Nat′

    -- Within reason, of course.  It's not really reasonable to assume that _+_ can
    -- take two differently sized `small' copies of Nat and put the result in some
    -- `huge' copy, or that id should move its input into a different universe level:
    id : ∀ {ℓ} → {A : Set ℓ} → A → A
    id x = x

    _+′_ : ∀ {ℓ} → Nat′ {ℓ} → Nat′ {ℓ} → Nat′ {ℓ}
    zero′   +′ n = n
    succ′ m +′ n = succ′ (m +′ n)

    -- Generality is offset against Agda's inability to infer correct universe levels.
    -- The more universe polymorphism that is inserted, the more work you have to do
    -- to help Agda along with its type inference.  So some balance is required, but
    -- for a heuristic things like data types (e.g. Nat′) above and records (e.g. Four)
    -- should always float, and take things from there.
  
  module AnAlgebraicHierarchy where

    open import Level

    open import Data.Product

    open import Relation.Binary.PropositionalEquality

    -- We will now look at how to properly capture algebraic structures in Agda,
    -- building on what we did with Monoid.

    -- A Magma has a single binary operation _·_.  Let's define binary operations:

    BinaryOperation : ∀ {ℓ} → Set ℓ → Set ℓ
    BinaryOperation A = A → A → A

    -- And define a record capturing Magmas.  Note there are no laws associated
    -- with a Magma:

    record Magma {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
      field
        Carrier : Set ℓ
        _·_     : BinaryOperation Carrier

    -- A Semigroup is a Magma where the binary operation _·_ is known to be
    -- associative:

    IsAssociative : ∀ {ℓ} → {A : Set ℓ} → BinaryOperation A → Set ℓ
    IsAssociative _·_ = ∀ x y z → (x · (y · z)) ≡ ((x · y) · z)

    -- This record carries the laws associated with a semigroup:
    record IsSemigroup {ℓ} {Carrier : Set ℓ} (_·_ : Carrier → Carrier → Carrier) : Set (Level.suc ℓ) where
      field
        is-associative : IsAssociative _·_

    -- This record packages a Carrier type, the binary operation, and the laws
    -- all together.
    record Semigroup {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
      field
        Carrier      : Set ℓ
        _·_          : BinaryOperation Carrier
        is-semigroup : IsSemigroup _·_

      -- Open the is-semigroup record inside this one, so all of the laws
      -- are available in here.
      open IsSemigroup is-semigroup public

      -- Inside the Semigroup module, we provide a function for moving *down*
      -- the algebraic hierarchy to obtain a Magma from our Semigroup.  When
      -- we `open Semigroup some-semigroup' in a context, this function is
      -- then available to turn a semigroup into a magma.  Note we have to
      -- help Agda out with the universe levels.
      magma : Magma {ℓ} {ℓ′}
      magma = record { Carrier = Carrier ; _·_ = _·_ }

    -- A monoid is a semigroup with a left and right identity element:

    IsLeftIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinaryOperation A → Set ℓ
    IsLeftIdentity ε _·_ = ∀ x → (ε · x) ≡ x

    IsRightIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinaryOperation A → Set ℓ
    IsRightIdentity ε _·_ = ∀ x → (x · ε) ≡ x

    -- Recall that _×_ is Agda's method of encoding logical conjunction:
    IsIdentity : ∀ {ℓ} → {A : Set ℓ} → A → BinaryOperation A → Set ℓ
    IsIdentity ε _·_ = IsLeftIdentity ε _·_ × IsRightIdentity ε _·_

    record IsMonoid {ℓ} {Carrier : Set ℓ} (ε : Carrier) (_·_ : BinaryOperation Carrier) : Set (Level.suc ℓ) where
      field
        is-semigroup : IsSemigroup _·_
        is-identity  : IsIdentity ε _·_

      -- For ease of use we put some utility lemmas in this record so we don't
      -- have to keep destructuring the pair all the time when we come to prove
      -- things about monoids:
      is-left-identity : IsLeftIdentity ε _·_
      is-left-identity = proj₁ is-identity

      is-right-identity : IsRightIdentity ε _·_
      is-right-identity = proj₂ is-identity

      -- Import all the semigroup laws (e.g. associativity):
      open IsSemigroup is-semigroup public

    record Monoid {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
      field
        Carrier   : Set ℓ
        ε         : Carrier
        _·_       : BinaryOperation Carrier

        is-monoid : IsMonoid ε _·_

      open IsMonoid is-monoid public

      semigroup : Semigroup {ℓ} {ℓ′}
      semigroup = record { Carrier = Carrier ; _·_ = _·_ ; is-semigroup = is-semigroup }

      magma : Magma {ℓ} {ℓ′}
      magma = record { Carrier = Carrier ; _·_ = _·_ }

    -- EXERCISE: capture commutative (Abelian) and idempotent monoids using two new
    -- sets of records below:

    IsCommutative : ∀ {ℓ} → {A : Set ℓ} → BinaryOperation A → Set ℓ
    IsCommutative _·_ = ∀ x y → (x · y) ≡ (y · x)

    record IsCommutativeMonoid {ℓ} {Carrier : Set ℓ} (ε : Carrier) (_·_ : BinaryOperation Carrier) : Set (Level.suc ℓ) where
      field
        is-monoid      : IsMonoid ε _·_
        is-commutative : IsCommutative _·_

      open IsMonoid is-monoid public

    record CommutativeMonoid {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
      field
        Carrier               : Set ℓ
        ε                     : Carrier
        _·_                   : BinaryOperation Carrier

        is-commutative-monoid : IsCommutativeMonoid ε _·_

      open IsCommutativeMonoid is-commutative-monoid public

      monoid : Monoid {ℓ} {ℓ′}
      monoid = record { Carrier = Carrier ; _·_ = _·_ ; is-monoid = is-monoid }

    IsIdempotent : ∀ {ℓ} → {A : Set ℓ} → BinaryOperation A → Set ℓ
    IsIdempotent _·_ = ∀ x → (x · x) ≡ x

    record IsIdempotentMonoid {ℓ} {Carrier : Set ℓ} (ε : Carrier) (_·_ : BinaryOperation Carrier) : Set (Level.suc ℓ) where
      field
        is-monoid     : IsMonoid ε _·_
        is-idempotent : IsIdempotent _·_

      open IsMonoid is-monoid public

    record IdempotentMonoid {ℓ ℓ′} : Set (Level.suc (ℓ Level.⊔ ℓ′)) where
      field
        Carrier : Set ℓ
        ε : Carrier
        _·_ : BinaryOperation Carrier

        is-idempotent-monoid : IsIdempotentMonoid ε _·_

      open IsIdempotentMonoid is-idempotent-monoid public

      monoid : Monoid {ℓ} {ℓ′}
      monoid = record { Carrier = Carrier ; _·_ = _·_ ; is-monoid = is-monoid }

    -- Note how Agda can have parameterised modules.  The effect is to `fix' a monoid
    -- in the body of the module below.  When we try to open DerivedMonoidalProperties
    -- later we must supply a monoid to open the module with.  All of the lemmas and
    -- definitions below will then become specialised to that monoid.
    module DerivedMonoidalProperties {ℓ ℓ′} (m : Monoid {ℓ} {ℓ′}) where

      -- Open m.  Note how Carrier, ε, _·_ and so on are now in scope.  Further, so
      -- are all the laws like is-associative, is-left-identity, and so on, as well
      -- as the functions to obtain a magma and semigroup from m:
      open Monoid m

      -- Prove that identities in monoids are unique:
      identities-are-unique : ∀ ε′ → IsIdentity ε′ _·_ → ε′ ≡ ε
      identities-are-unique ε′ (left-id , right-id) = trans lemma₁ lemma₂
        where
          lemma₁ : ε′ ≡ ε · ε′
          lemma₁ = sym (is-left-identity ε′)

          lemma₂ : ε · ε′ ≡ ε
          lemma₂ = right-id ε

      open import Data.List renaming (List to List′)

      -- Our previous definition of monoidal folds.  Note how simple the type is due
      -- to opening m above:
      fold : List′ Carrier → Carrier
      fold []       = ε
      fold (x ∷ xs) = x · fold xs

      -- We can also define a notion of `power' in a monoid:
      pow : Carrier → ℕ → Carrier
      pow base  ℕ.zero   = ε
      pow base (ℕ.suc e) = base · pow base e

      -- And prove some properties of it reminiscent of the familiar `laws of exponents':
      pow-+ : ∀ base m n → pow base (m + n) ≡ pow base m · pow base n
      pow-+ base  ℕ.zero   n = sym (is-left-identity (pow base n))
      pow-+ base (ℕ.suc m) n
        rewrite pow-+ base m n = is-associative base (pow base m) (pow base n)

      -- EXERCISE: Try to prove the following: ∀base. pow base 1 ≡ base
      pow-1 : ∀ base → pow base 1 ≡ base
      pow-1 = is-right-identity

  -- EXERCISE: you insert a parameterised module here that `fixes' a commutative monoid,
  -- as you defined earlier.  Define an ordering using that monoid, where
  --     x ≤ y     if and only if      ∃z. x · z ≡ y
  -- Show that the ordering is reflexive and transitive (that is, the ordering is a quasi-
  -- order, or pre-order).

    module DerivedCommutativeMonoidalProperties {ℓ ℓ′} (m : CommutativeMonoid {ℓ} {ℓ′}) where

      open CommutativeMonoid m

      _≤″_ : Carrier → Carrier → Set ℓ
      x ≤″ y = Σ[ z ∈ Carrier ] x · z ≡ y
      -- what's wrong with these two?
      -- x ≤″ y = ∃ Carrier (λ z → x · y ≡ z)
      -- x ≤″ y = (Carrier , λ z → x · y ≡ z)

      ≤″-reflexive : (x : Carrier) → x ≤″ x
      ≤″-reflexive x = (ε , is-right-identity x)

      ≤″-transitive : (x y z : Carrier) → x ≤″ y → y ≤″ z → x ≤″ z
      ≤″-transitive x y z (w₁ , x·w₁≡y) (w₂ , y·w₂≡z) = (w₁ · w₂) , prf
        where
          prf : x · (w₁ · w₂) ≡ z
          prf rewrite is-associative x w₁ w₂ | x·w₁≡y | y·w₂≡z = refl

  module YetMoreExercises where

    open import Level

    open import Function

    -- We rename to avoid clashes with names we have introduced ourselves in the file
    -- above:
    open import Data.Empty
    open import Data.List renaming (List to List′; _∷_ to _∷′_)
    open import Data.Product
    open import Data.Unit renaming (⊤ to ⊤″)

    open import Relation.Binary.PropositionalEquality
    open import Relation.Binary
    open import Relation.Nullary

    -- We work in a module that `fixes' both a type, `A', and a proof that equality at that
    -- type is decidable.  By `decidable', we mean that for any two elements of `A' we can
    -- case split on whether `x ≡ y' or `x ≢ y' via pattern matching.
    module AssumingDecidableEquality {ℓ} {A : Set ℓ} (≡-decidable : Decidable (_≡_ {ℓ} {A})) where

      -- Utility function for below.  In Agda, all constructors are injective and Agda's
      -- unification algorithm knows this fact.  In some cases, however, we cannot rely on
      -- unification to solve a goal but must use an explicit lemma restating the injectivity
      -- of various constructors.  I'm sure this is somewhere in the standard library, but it
      -- is so simple to prove there's no point wasting time trying to find it:
      ∷-injective : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → {xs ys : List′ A} → x ∷′ xs ≡ y ∷′ ys → x ≡ y × xs ≡ ys
      ∷-injective refl = refl , refl

      -- Lists inherit decidable equality if their elements enjoy the same property.
      -- We demonstrate this fact by case analysis on the two lists, like so:
      ≡-List-decidable : Decidable (_≡_ {ℓ} {List′ A})
      -- If the two elements are equal we use the `yes' constructor of the Dec data
      -- type.  yes expects a proof that [] ≡ [] (i.e. xs ≡ ys in this case).  This is
      -- simply refl:
      ≡-List-decidable []        []        = yes refl
      -- If the two elements are not equal, we use the `no' constructor of the Dec data
      -- type.  no expects a proof that [] ≢ y ∷ ys, i.e. that [] ≡ y ∷ ys → ⊥.  Note
      -- that this is a function type, so inhabited by a λ-abstraction that takes a
      -- term of type [] ≡ y ∷ ys to a term of type ⊥.  [] ≡ y ∷ ys is absurd as Agda knows
      -- that there is no way to inhabit this type, so we can discharge our proof obligation
      -- with an absurd pattern ().
      ≡-List-decidable []        (y ∷′ ys) = no (λ ())
      -- The same:
      ≡-List-decidable (x ∷′ xs) []        = no (λ ())
      -- This is the interesting case.  We must do two things: check the heads of the
      -- lists are equal and check the tails of the lists are equal to be able to decide
      -- whether both lists are identical.  In the first case, we pattern match on the
      -- result of ≡-decidable x y and in the second case we pattern match on the recursive
      -- call to ≡-List-decidable xs ys.  The `with' syntax is how we pattern match, with
      -- the | stating we are performing more than one analysis at once.  In the first
      -- case below, prf₁ will have type x ≡ y and prf₁′ will have xs ≡ ys, whereas in
      -- the third case below, prf₃ will have x ≢ y (i.e. x ≡ y → ⊥) and prf₃′ will have
      -- type xs ≢ ys.  In all cases, we use these proofs to help construct the required
      -- element of the Dec data type:
      ≡-List-decidable (x ∷′ xs) (y ∷′ ys) with ≡-decidable x y | ≡-List-decidable xs ys
      ... | yes prf₁ | yes prf₁′
        rewrite prf₁ | prf₁′ = yes refl
      ... | yes prf₂ | no  prf₂′ = no (λ p → prf₂′ ∘ proj₂ ∘ ∷-injective $ p)
      ... | no  prf₃ | no  prf₃′ = no (λ p → prf₃′ ∘ proj₂ ∘ ∷-injective $ p)
      ... | no  prf₄ | yes prf₄′ = no (λ p → prf₄ ∘ proj₁ ∘ ∷-injective $ p)

      -- You may want to comment some of the parts of the function above out, replace them
      -- with metavariables, and look at the types to understand what is going on in
      -- ≡-List-decidable.

      -- The unit type has a trivial decidable equality:
      ≡-⊤-decidable : Decidable (_≡_ {A = ⊤″})
      ≡-⊤-decidable tt tt = yes refl

      -- EXERCISE: show that the natural numbers, ℕ, have a decidable equality:
      -- ∷-injective : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → {xs ys : List′ A} → x ∷′ xs ≡ y ∷′ ys → x ≡ y × xs ≡ ys
      suc-injective : {m n : ℕ} → ℕ.suc m ≡ ℕ.suc n → m ≡ n
      suc-injective refl = refl

      ≡-ℕ-decidable : Decidable (_≡_ {A = ℕ})
      ≡-ℕ-decidable ℕ.zero    ℕ.zero    = yes refl
      ≡-ℕ-decidable ℕ.zero    (ℕ.suc n) = no (λ ())
      ≡-ℕ-decidable (ℕ.suc m) ℕ.zero    = no (λ ())
      ≡-ℕ-decidable (ℕ.suc m) (ℕ.suc n) with ≡-ℕ-decidable m n
      ... | yes prf₁
        rewrite prf₁ = yes refl
      ... | no prf₂ = no (λ p → prf₂ ∘ suc-injective $ p)
