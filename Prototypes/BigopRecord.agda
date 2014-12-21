module Prototypes.BigopRecord where

  open import Data.Bool
  open import Data.Maybe
  open import Algebra
  open import Algebra.FunctionProperties.Core
  open import Algebra.Structures
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat

  open import Level
    renaming (zero to zeroℓ; suc to sucℓ; _⊔_ to _⊔ℓ_)

--  record Bigop {a b i} (A : Set a) (B : Set b) (Index : Set i) : Set _ where
--    field
--      ⟦_⟧  : Index → Maybe A
--      _⊕_  : B → A → B
--      ε    : B

  record Bigop′ {c ℓ} : Set (sucℓ (c ⊔ℓ ℓ)) where
    constructor  _⦇_,_⦈_
    infixl 7 _∙_
    field
      Carrier     : Set c
      -- need more restrictions on Carrier. must be "enumerable", finite, ...
      ε           : Carrier
      _∙_         : Op₂ Carrier
      isMonoid    : IsMonoid _≡_ _∙_ ε

    open IsMonoid isMonoid public

  ∑ : Bigop′ {zeroℓ} {zeroℓ}
  ∑ = ℕ ⦇ zero , _+_ ⦈ isMonoid
    where
      isMonoid : IsMonoid _≡_ _+_ zero
      isMonoid = {!!}

--  eval : ∀ {c i ℓ} {Carrier : Set c} {ε : Carrier} {_∙_ : Op₂ Carrier} {I : Set i} {isMonoid : IsMonoid _≡_ _∙_ ε}
--         → (b : Carrier ⦇ ε , _∙_ ⦈ isMonoid) → (I → Bool) → (I → c)
--  eval x y = ?

  eval : ∀ {c i ℓ} {I : Set i} → (b : Bigop′ {c} {ℓ}) → (I → Bool) → (I → Bigop′.Carrier b) → Bigop′.Carrier b
  eval b p f = {!!}
    where
      open Bigop′ b

--  record Bigop

--  ⨁ : Bigop 
--  ⨁ = ⦇ ε , _⊕_ ⦈
