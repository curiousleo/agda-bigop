module Prototypes.BigopRecord where

  open import Data.Bool
  open import Data.Maybe
  open import Algebra
  open import Algebra.FunctionProperties.Core
  open import Algebra.Structures
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Data.Vec

  open import Level
    renaming (zero to zeroℓ; suc to sucℓ; _⊔_ to _⊔ℓ_)

--  record Bigop {a b i} (A : Set a) (B : Set b) (Index : Set i) : Set _ where
--    field
--      ⟦_⟧  : Index → Maybe A
--      _⊕_  : B → A → B
--      ε    : B

  mutual
    data UVec {a} (A : Set a) : ℕ → Set a where
      []     : UVec A zero
      _∷_[_] : {n : ℕ} → (a : A) → (as : UVec A n) → a ♯ as → UVec A (suc n)

    _♯_ : ∀ {a} → {n : ℕ} → {A : Set a} → A → UVec A n → Set
    a ♯ as = {!!}

  IsEnumerable : ∀ {c} → (Carrier : Set c) → (n : ℕ) → UVec {c} Carrier n
  IsEnumerable = {!!}

  record FinType {c ℓ} {n : ℕ} : Set (c ⊔ℓ ℓ) where
    field
      Carrier      : Set c
      isEnumerable : IsEnumerable {c} Carrier n

  record Bigop′ {c ℓ} {n : ℕ} : Set (sucℓ (c ⊔ℓ ℓ)) where
    constructor  _⦇_,_⦈_
    infixl 7 _∙_
    field
      Carrier     : FinType {c} {n}
      -- need more restrictions on Carrier. must be "enumerable", finite, ...
      ε           : FinType.Carrier Carrier
      _∙_         : Op₂ (FinType.Carrier Carrier)
      isMonoid    : IsMonoid _≡_ _∙_ ε

    open IsMonoid isMonoid public

  ∑ : Bigop′
  ∑ = {!!} ⦇ zero , _+_ ⦈ isMonoid
    where
      isMonoid : IsMonoid _≡_ _+_ zero
      isMonoid = record { isSemigroup = record { isEquivalence = {!!} ; assoc = {!!} ; ∙-cong = {!!} } ; identity = {!!} }

--  eval : ∀ {c i ℓ} {Carrier : Set c} {ε : Carrier} {_∙_ : Op₂ Carrier} {I : Set i} {isMonoid : IsMonoid _≡_ _∙_ ε}
--         → (b : Carrier ⦇ ε , _∙_ ⦈ isMonoid) → (I → Bool) → (I → c)
--  eval x y = ?

  eval : ∀ {c i ℓ} {I : Set i} → (b : Bigop′ {c} {ℓ}) → (I → Bool) → (I → FinType.Carrier(Bigop′.Carrier b)) → FinType.Carrier (Bigop′.Carrier b)
  eval b p f = {!!}
    where
      open Bigop′ b

--  record Bigop

--  ⨁ : Bigop 
--  ⨁ = ⦇ ε , _⊕_ ⦈
