module Prototypes.BigopRecord where

  open import Data.Bool
  open import Data.Maybe
  open import Algebra
  open import Algebra.FunctionProperties.Core
  open import Algebra.Structures
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  import Data.Fin as Fin
  open import Data.Vec

  open import Level
    renaming (zero to zeroℓ; suc to sucℓ; _⊔_ to _⊔ℓ_)

--  record Bigop {a b i} (A : Set a) (B : Set b) (Index : Set i) : Set _ where
--    field
--      ⟦_⟧  : Index → Maybe A
--      _⊕_  : B → A → B
--      ε    : B

  
  data UVec {a} (A : Set a) : ℕ → Set a
  _♯_ : ∀ {a} → {n : ℕ} → {A : Set a} → A → UVec {a} A n → Set

  data UVec {a} A where
    []     : UVec A zero
    _∷_[_] : {n : ℕ} → (x : A) → (xs : UVec {a} A n) → x ♯ xs → UVec A (suc n)

  a ♯ as = {!!}

  record FinType {c ℓ} {n : ℕ} : Set (sucℓ (c ⊔ℓ ℓ)) where
    field
      Carrier      : Set c
      isEnumerable : UVec {c} Carrier n

  record Foldable {ℓ} : Set (sucℓ ℓ) where
    field
      Fold : ∀ (T : ℕ → Set) {m} →
       (∀ {n} → T n → T (suc n)) →
       (∀ {n} → T (suc n)) →
       Fin.Fin m → T m

  record Bigop′ {c ℓ} {n : ℕ} : Set (sucℓ (c ⊔ℓ ℓ)) where
    constructor  _⦇_,_⦈_
    infixl 7 _∙_
    field
      Carrier     : FinType {c} {zeroℓ} {n}
      -- need more restrictions on Carrier. must be "enumerable", finite, ...
      ε           : FinType.Carrier Carrier
      _∙_         : Op₂ (FinType.Carrier Carrier)
      isMonoid    : IsMonoid _≡_ _∙_ ε

    open IsMonoid isMonoid public

  ∑ : Bigop′ {zeroℓ} {zeroℓ} {_}
  ∑ = {!!} ⦇ Fin.zero , Fin._+_ ⦈ isMonoid
    where
      isMonoid : IsMonoid _≡_ Fin._+_ Fin.zero
      isMonoid = record { isSemigroup = record { isEquivalence = {!!} ; assoc = {!!} ; ∙-cong = {!!} } ; identity = {!!} }

--  eval : ∀ {c i ℓ} {Carrier : Set c} {ε : Carrier} {_∙_ : Op₂ Carrier} {I : Set i} {isMonoid : IsMonoid _≡_ _∙_ ε}
--         → (b : Carrier ⦇ ε , _∙_ ⦈ isMonoid) → (I → Bool) → (I → c)
--  eval x y = ?

  eval : ∀ {c i ℓ} {I : Set i} → {n : ℕ} → (b : Bigop′ {c} {ℓ} {n}) → (I → Bool) → (I → FinType.Carrier(Bigop′.Carrier b)) → FinType.Carrier (Bigop′.Carrier b)
  eval b p f = {!!}
    where
      open Bigop′ b

--  record Bigop

--  ⨁ : Bigop 
--  ⨁ = ⦇ ε , _⊕_ ⦈
