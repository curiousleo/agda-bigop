open import Relation.Binary

module Data.List.Sorted
  {a ℓ₁ ℓ₂}
  (totalOrder : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Level

open import Data.Empty using (⊥-elim)
open import Data.List.Base
open import Data.Nat.Base hiding (_⊔_; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Function

open import Relation.Nullary

open DecTotalOrder totalOrder
  renaming (trans to ≤-trans; refl to ≤-refl)

-- XXX: standard library candidate
¬x≤y→y≤x : ∀ {x y} → ¬ (x ≤ y) → y ≤ x
¬x≤y→y≤x {x} {y} prf with total x y
... | inj₁ p = ⊥-elim ∘ prf $ p
... | inj₂ p = p

mutual
 
  data SortedList : Set (ℓ₂ ⊔ a) where
    []     : SortedList
    _∷_⟨_⟩ : (y : Carrier) → (ys : SortedList) → (y≼ys : y ≼ ys)
             → SortedList

  _≼_ : Carrier → SortedList → Set ℓ₂
  x ≼ []               = Lift ⊤
  x ≼ (y ∷ ys ⟨ y≼ys ⟩) = x ≤ y × x ≼ ys

≼-trans : ∀ {x y} → (ys : SortedList) → y ≼ ys → x ≤ y → x ≼ ys
≼-trans []               xsDomx         y≤x = lift tt
≼-trans (z ∷ zs ⟨ prf ⟩) (x≤z , zsDomx) y≤x = ≤-trans y≤x x≤z , ≼-trans zs zsDomx y≤x

mutual

  insert : Carrier → SortedList → SortedList
  insert x []               = x ∷ [] ⟨ lift tt ⟩
  insert x (y ∷ ys ⟨ y≼ys ⟩) with x ≤? y
  ... | yes lt = x ∷ y ∷ ys ⟨ y≼ys ⟩ ⟨ lt , ≼-trans ys y≼ys lt ⟩
  ... | no ¬lt = y ∷ insert x ys ⟨ ≼-insert ys (¬x≤y→y≤x ¬lt) y≼ys ⟩

  ≼-insert : ∀ {x y} → (ys : SortedList) → y ≤ x → y ≼ ys → y ≼ (insert x ys)
  ≼-insert {x} []                y≤x dom = y≤x , lift tt
  ≼-insert {x} (z ∷ zs ⟨ z≼zs ⟩) y≤x (y≤z , zsDomy) with x ≤? z
  ... | yes lt = y≤x , y≤z , zsDomy
  ... | no ¬lt = y≤z , ≼-insert zs y≤x zsDomy


toList : SortedList → List Carrier
toList []                = []
toList (y ∷ ys ⟨ y≼ys ⟩) = y ∷ toList ys

fromList : List Carrier → SortedList
fromList = foldr insert []


data _∈_ (x : Carrier) : SortedList → Set (ℓ₁ ⊔ a ⊔ ℓ₂) where
  here  : (xs : SortedList) → ∀ prf → x ∈ x ∷ xs ⟨ prf ⟩
  there : (y : Carrier) → (ys : SortedList) → ∀ prf → x ∈ ys → x ∈ y ∷ ys ⟨ prf ⟩
