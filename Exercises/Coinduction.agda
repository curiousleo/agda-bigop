{-# OPTIONS --copatterns #-}

module Exercises.Coinduction where

  -- Induction allows us to construct data in a `bottom-up' manner.  For example,
  -- lists are constructed by asserting the existence of a `bottom' element, the
  -- empty list, [], and providing a means of constructing new, larger lists from
  -- old, via consing, _∷_.  This `bottom-up' construction of data necessarily
  -- implies that the data being constructed will be finite.  For instance, all
  -- Agda lists have a finite though unbounded length.  Recursion, the counterpart
  -- to induction, is the means by which we deconstruct such data, and for
  -- soundness reasons all recursive calls must occur on subterms of an input
  -- parameter, to ensure termination.

  -- But what about infinite data?  Infinite streams of bits, for example, cannot
  -- be shoehorned into this framework.  For such data, we need coinduction and
  -- corecursion, the duals of induction and recursion.  But now, clearly,
  -- corecursion cannot ever `terminate' in the way that recursion can, but how
  -- does this not introduce an unsoundness into Agda's logic?  The answer being
  -- that there is a dual notion of termination for corecursion, called `productivity'.
  -- If every recursive call has to be terminating, then every corecursive call
  -- has to be productive.

  -- Agda has two mechanisms for corecursion, `musical notation' being the older
  -- mechanism (and has always seemed a little dodgy to me, it has to be said), and
  -- the second, copatterns, being an experimental new feature.  We examine the two
  -- in turn:

  -- Import the musical notation, and machinery necessary for working with
  -- coinduction:

  open import Coinduction

  -- Let's define streams of bits

  open import Data.Bool
  open import Data.List
    renaming (_∷_ to _∷ₗ_) hiding (map; length; zipWith; drop; take)

  Bit : Set
  Bit = Bool

  -- Agda's musical notation mechanism merges data and codata declarations so that
  -- they are under a single construct.  The ∞ type constructor marks Stream as
  -- being codata.  For an imprecise mental model that mostly works, think of
  -- ∞ as introducing some `lazy' data.

  -- Note streams really are infinite: there's no `base case', the empty stream,
  -- here at all:

  data Stream : Set where
    _∷_ : Bit → ∞ Stream → Stream

  -- Defining the head of a stream is easy, and works just as for lists:

  head : Stream → Bit
  head (x ∷ xs) = x

  -- Defining the tail of a stream is a little more difficult.  Below, x has type
  -- Bit whereas xs has type ∞ Stream.  We need to get from ∞ Stream to Stream.  For
  -- this we use ♭ which is of type {A : Set} → ∞ A → A.
  -- If ∞ introduces some lazy data, think of ♭ as `forcing' that lazy data to produce
  -- a value.

  tail : Stream → Stream
  tail (x ∷ xs) = ♭ xs

  -- Now we try to write map.  Below xs again has type ∞ Stream, and a naive call to
  -- maps f xs will not work, as map expects its second argument to have type Stream.
  -- So, once more we must `force' xs and obtain a Stream from ∞ Stream.  But then we
  -- have another problem, in that map f (♭ xs) has type Stream, but _∷_ expects its
  -- second argument to have type ∞ Stream, so we must `suspend' the corecursive
  -- call with ♯ (now you can see why this notation is called `musical'):

  map : (Bit → Bit) → Stream → Stream
  map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

  -- Try writing the above without the musical notation, and see the type errors you
  -- get.

  -- We can write functions on Streams that are impossible with list, due to a lack
  -- of termination.  For instance:

  repeat : Bit → Stream
  repeat x = x ∷ ♯ repeat x

  -- Having said that, there's functions on lists that we cannot define on Stream.
  -- Try writing the following, for instance:

  open import Data.Nat

  -- Above, you can write something that looks like it should work (i.e. all the type
  -- are correct), but Agda complains about what you have written by colouring in
  -- the corecursive call with a salmon colour, the colour used to mark non-terminating
  -- functions.  Why?  The answer is that Agda has recognised the length function above
  -- as being non-productive.  To a first approximation, a `productive' function must
  -- have `guarded' corecursive calls, for instance:
  --     foo (x ∷ xs) = foo …
  -- The above definition instead has the following:
  --     length (x ∷ xs) = suc (length …)
  -- Where suc, a constructor, is `above' the corecursive call to length.  This isn't
  -- permitted!

  -- EXERCISE: try to define the following functions on Streams:

  zipWith : (Bit → Bit → Bit) → Stream → Stream → Stream
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ zipWith f (♭ xs) (♭ ys)

  drop : ℕ → Stream → Stream
  drop zero      xs = xs
  drop (suc cnt) xs = drop cnt xs

  open import Data.Vec
    hiding (head ; tail ; take)

  take : (m : ℕ) → Stream → Vec Bit m
  take zero      xs       = []
  take (suc cnt) (x ∷ xs) = x ∷ (take cnt (♭ xs))

  -- Some definitions are more naturally expressed as a relation, captured by an indexed
  -- data type.  For instance:

  data _In_ : Bit → Stream → Set where
    here  : ∀ x xs → x In (x ∷ xs)
    there : ∀ {x ys} → ∀ y → x In (♭ ys) → x In (y ∷ ys)

  -- But what about equality?  Remember _≡_ is defined as a data type in
  -- Relation.Binary.PropositionalEquality (it is the smallest reflexive relation).
  -- How can we use this definition to establish that two infinite streams are equal?
  -- We can't, and we must give a new definition specialised for Streams.

  -- EXERCISE: Try to give an inductive definition of equality between Streams.  You
  -- can of course use _≡_ to establish the equality of _data_ in the definition
  -- below:

  open import Relation.Binary.PropositionalEquality
 
  -- XXX: This works, but I think it can be more naturally expressed as in _≈′_ below:

  data _≈_ : Stream → Stream → Set where
    refl : ∀ {xs ys} → (head xs) ≡ (head ys) → (tail xs) ≈ (tail ys)

  data _≈′_ : Stream → Stream → Set where
    refl : ∀ {x y xs ys} → x ≡ y → (♭ xs) ≈′ (♭ ys) → (x ∷ xs) ≈′ (y ∷ ys)

  -- As you can see, working with musical notation is not particularly hard, and if you
  -- maintain the mental model of ♭ being `force' and ♯ being `suspend' for infinite
  -- data introduced with ♯ then it's easy to follow your intuition and arrive at a
  -- correct definition.  But ∞, ♭ and ♯ don't really highlight how induction and
  -- recursion are dual to coinduction and corecursion.  Agda's new copatterns feature
  -- is meant to highlight exactly that duality.  First, we turn on the necessary
  -- extension:

  -- {-# OPTIONS --copatterns #-} (see top of file, this pragma can only go there)

  -- We now define Stream′ as a record:

  record Stream′ : Set where
    coinductive
    field
      head′ : Bit
      tail′ : Stream′

  -- Note the record is recursive: tail′ has type Stream′ (′ is used to avoid name
  -- clashes with the definitions above).  The `coinductive' keyword is necessary
  -- to convince Agda's productivity checker that everything is kosher below (and
  -- establishes that Stream′ is a coinductive definition, of course).  Remove the
  -- keyword above and watch as repeat′ is coloured salmon below.

  -- Open the Stream′ record to make head′ and tail′ visible without having to be
  -- fully qualified, a la Stream′.head′

  open Stream′

  -- Now lets define repeat′:

  repeat′ : Bit → Stream′
  head′ (repeat′ x) = x
  tail′ (repeat′ x) = repeat′ x

  -- Notice the difference between a pattern and a copattern?  It should be obvious
  -- what is going on: functions are defined using copatterns by stating how they
  -- commute with head′ and tail′.  You can read more about copatterns in this
  -- paper, if you are interested: http://www.cs.mcgill.ca/~bpientka/papers/icfp13.pdf.
  -- Some more examples:

  map′ : (Bit → Bit) → Stream′ → Stream′
  head′ (map′ f xs) = f (head′ xs)
  tail′ (map′ f xs) = map′ f (tail′ xs)

  zipWith′ : (Bit → Bit → Bit) → Stream′ → Stream′ → Stream′
  head′ (zipWith′ f xs ys) = f (head′ xs) (head′ ys)
  tail′ (zipWith′ f xs ys) = zipWith′ f (tail′ xs) (tail′ ys)

  -- EXERCISE: you try to define the following:

  evens′ : Stream′ → Stream′
  head′ (evens′ xs) = head′ xs
  tail′ (evens′ xs) = tail′ (tail′ xs)
 
  drop′ : ℕ → Stream′ → Stream′
  head′ (drop′ zero      xs) = head′ xs
  head′ (drop′ (suc cnt) xs) = head′ (drop′ cnt (tail′ xs))
  tail′ (drop′ zero      xs) = tail′ xs
  tail′ (drop′ (suc cnt) xs) = tail′ (drop′ cnt (tail′ xs))

  take′ : (m : ℕ) → Stream′ → Vec Bit m
  take′ zero      xs = []
  take′ (suc cnt) xs = head′ xs ∷ take′ cnt (tail′ xs)

  open import Level
    renaming (zero to zeroℓ; suc to sucℓ; _⊔_ to _⊔ℓ_)

  -- QUESTION: How do I do this with explicit levels?
  -- XXX: like this:
  -- Remember any type (such as A below) has to be given a type itself!
  record Stream″ {ℓ ℓ′} (A : Set ℓ) : Set (ℓ ⊔ℓ ℓ′) where
    coinductive
    field
      head″ : A
      -- Agda gets confused here trying to infer the correct levels, and so
      -- you need to help it out by passing in the correct levels as explicit
      -- parameters:
      tail″ : Stream″ {ℓ} {ℓ′} A
      
  open Stream″

  map″ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A → B) → Stream″ {ℓ} {ℓ′} A → Stream″ {ℓ′} {ℓ} B
  head″ (map″ f xs) = f (head″ xs)
  tail″ (map″ f xs) = map″ f (tail″ xs)
 
  -- XXX: this can also be written like drop‴ below:
  drop″ : ∀ {ℓ ℓ′} {A : Set ℓ} → ℕ → Stream″ {ℓ} {ℓ′} A → Stream″ A
  head″ (drop″ zero xs) = head″ xs
  head″ (drop″ (suc n) xs) = head″ (drop″ n (tail″ xs))
  tail″ (drop″ zero xs) = xs
  tail″ (drop″ (suc n) xs) = tail″ (drop″ n (tail″ xs))

  -- Remember, here ℕ is data, and so you can do recursive calls on the first
  -- argument, but Stream″ is codata.  Essentially drop is a recursive function
  -- that just happens to take a codata argument.  Data and codata can be
  -- mixed freely in all functions!
  drop‴ : ∀ {ℓ ℓ′ A} → ℕ → Stream″ {ℓ} {ℓ′} A → Stream″ {ℓ} {ℓ′} A
  drop‴ zero      xs = xs
  drop‴ (suc cnt) xs = drop‴ cnt (tail″ xs)

  count : ∀ {ℓ′} (from : ℕ) → Stream″ {zeroℓ} {ℓ′} ℕ
  head″ (count from) = from
  tail″ (count from) = count (suc from)

  nats : ∀ {ℓ′} → Stream″ {zeroℓ} {ℓ′} ℕ
  nats = count zero

  -- QUESTION: What's an appropriate notion of equality for streams defined in this way?

  -- XXX: something like this should work.  Two streams are equal if they are observably
  -- equal at their heads and observably equal at their tails:

  record _≈″_ (xs ys : Stream′) : Set where
    coinductive
    field
      ≈-head : head′ xs ≡  head′ ys
      ≈-tail : tail′ xs ≈″ tail′ ys

  open _≈″_

  record _≈‴_ {ℓ ℓ′} {A : Set ℓ} (xs ys : Stream″ {ℓ} {ℓ′} A) : Set (ℓ ⊔ℓ ℓ′) where
    coinductive
    field
      ≈‴-head : head″ xs ≡ head″ ys
      ≈‴-tail : tail″ xs ≈‴ tail″ ys

  open _≈‴_

  toStream″ : ∀ {ℓ′} → Stream′ → Stream″ {zeroℓ} {ℓ′} Bit
  head″ (toStream″ xs) = head′ xs
  tail″ (toStream″ xs) = toStream″ (tail′ xs)

  open import Relation.Binary

  ≈″-refl : Reflexive _≈″_
  ≈-head ≈″-refl = refl
  ≈-tail (≈″-refl {xs}) = ≈″-refl {tail′ xs}

  ≈″-sym  : Symmetric _≈″_
  ≈-head (≈″-sym prf) = sym (≈-head prf)
  ≈-tail (≈″-sym {xs} {ys} prf) = ≈″-sym {tail′ xs} {tail′ ys} (≈-tail prf)

  ≈″-trans : Transitive _≈″_
  ≈-head (≈″-trans xs≈″ys ys≈″zs) = trans (≈-head xs≈″ys) (≈-head ys≈″zs)
  ≈-tail (≈″-trans {xs} {ys} {zs} xs≈″ys ys≈″zs) = ≈″-trans {tail′ xs} {tail′ ys} {tail′ zs} (≈-tail xs≈″ys) (≈-tail ys≈″zs)

  -- EXERCISE: the above properties establish _≈″_ is a Setoid, i.e. an equivalence relation.
  -- What else do we need to know to establish that _≈″_ is an equality?  Can you show these
  -- properties?

  ≈″-equiv : IsEquivalence _≈″_
  ≈″-equiv = record { refl = ≈″-refl ; sym = ≈″-sym ; trans = ≈″-trans }
  
  spec : ∀ {n : ℕ} → head″ (drop″ n nats) ≡ n
  spec {zero}  = refl
  spec {suc n} =
    begin
      head″ (drop″ n (tail″ nats))
        ≡⟨ cong head″ (cong (drop″ n) lemma₀) ⟩
      head″ (drop″ n (map″ suc nats))
        ≡⟨ cong head″ lemma₁ ⟩
      head″ (map″ suc (drop″ n nats))
        ≡⟨ refl ⟩
      suc (head″ (drop″ n nats))
        ≡⟨ cong suc spec ⟩
      suc n
    ∎
    where
      open ≡-Reasoning

      lemma₀ : tail″ nats ≡ map″ suc nats
      lemma₀ = {!!}

      lemma₁ : ∀ {A B} {f : A → B} {xs : Stream″ A} → drop″ n (map″ f xs) ≡ map″ f (drop″ n xs)
      lemma₁ {f = f} {xs = xs} = {!!}
