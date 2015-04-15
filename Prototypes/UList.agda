module Prototypes.UList where

open import Level using (_⊔_)
open import Data.List renaming (_∷_ to _∷ᴸ_)
open import Data.List.Any
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary

-- Why is Data.Unit.⊤ not universe polymorphic?
record ⊤ {ℓ} : Set ℓ where
  constructor tt

[_]_∉_ : ∀ {c ℓ} (S : Setoid c ℓ) → (Setoid.Carrier S) → List (Setoid.Carrier S) → Set _
[ S ] x ∉ xs = x ∉ xs
  where open module M = Membership S

data UList {c ℓ} (S : Setoid c ℓ) : Set (c ⊔ ℓ)
toList : ∀ {c ℓ} {S : Setoid c ℓ} → UList S → List (Setoid.Carrier S)

data UList {c ℓ} S where
  []     : UList S
  _∷_[_] : (x : Setoid.Carrier S) (xs : UList S) → [ S ] x ∉ (toList xs) → UList S

toList []             = []
toList (x ∷ xs [ _ ]) = x ∷ᴸ toList xs

{-
-- Variant using an explicit relation rather than a setoid
data UList {a ℓ} (A : Set a) (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ)
_#_ : ∀ {a ℓ} → {A : Set a} {_≈_ : Rel A ℓ} → A → UList A _≈_ → Set ℓ

-- UList: a list with unique elements
data UList {a ℓ} A _≈_ where
  []     : UList A _≈_
  _∷_[_] : (x : A) (xs : UList A _≈_) → x # xs → UList A _≈_

x # [] = ⊤
_#_ {_≈_ = _≈_} x (y ∷ ys [ _ ]) = (¬ x ≈ y) × (x # ys)
-}

module URange where

  open import Data.Fin hiding (_+_)
  open import Data.List.All hiding (_∷_)
  open import Data.Nat
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality hiding (decSetoid)

  ≈-Fin : ∀ n → Rel (Fin n) Level.zero
  ≈-Fin n = DecSetoid._≈_ (decSetoid n)
    where
      open import Data.Fin.Properties using (decSetoid)

  countUp : (from len : ℕ) → UList (setoid ℕ)
  countUp from zero = []
  countUp from (suc len) = from ∷ count [ notin ]
    where
      count = countUp (suc from) len

      lt : All (_>_ from) (toList count)
      lt = {!!}

      noteq : All (_≢_ from) (toList count)
      noteq = {!!}

      notin : [ setoid ℕ ] from ∉ toList (countUp (suc from) len)
      notin isin = {!!}
