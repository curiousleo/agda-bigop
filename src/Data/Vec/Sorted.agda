open import Relation.Binary

module Data.Vec.Sorted
  {a ℓ₁ ℓ₂}
  (totalOrder : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Level

open import Data.Empty
open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Sum
open import Data.Unit
  hiding (_≤_; _≤?_; total)
open import Data.Vec
  using (Vec; foldr) renaming ([] to []′; _∷_ to _∷′_; _++_ to _++′_)

open import Function

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)
open import Relation.Nullary

open DecTotalOrder totalOrder
  renaming (trans to ≤-trans)
open IsEquivalence isEquivalence

-- XXX: standard library candidate
¬x≤y→y≤x : ∀ {x y} → ¬ (x ≤ y) → y ≤ x
¬x≤y→y≤x {x} {y} prf with total x y
... | inj₁ p = ⊥-elim (prf p)
... | inj₂ p = p

mutual
 
  data SortedVec : ℕ → Set (ℓ₂ ⊔ a) where
    []     : SortedVec 0
    _∷_⟨_⟩ : ∀ {n} → (x : Carrier) → (xs : SortedVec n) → xs Dominates x → SortedVec (ℕ.suc n)

  _Dominates_ : ∀ {n} → SortedVec n → Carrier → Set ℓ₂
  []               Dominates x = Lift ⊤
  (y ∷ ys ⟨ prf ⟩) Dominates x = (x ≤ y) × (ys Dominates x)

Dominates-trans : ∀ {n y x} → (xs : SortedVec n) → xs Dominates x → y ≤ x → xs Dominates y
Dominates-trans []               xsDomx         y≤x = lift tt
Dominates-trans (z ∷ zs ⟨ prf ⟩) (x≤z , zsDomx) y≤x = ≤-trans y≤x x≤z , Dominates-trans zs zsDomx y≤x

mutual

  insert : ∀ {n} → Carrier → SortedVec n → SortedVec (ℕ.suc n)
  insert x []               = x ∷ [] ⟨ lift tt ⟩
  insert x (y ∷ ys ⟨ prf ⟩) with x ≤? y
  ... | yes lt = x ∷ y ∷ ys ⟨ prf ⟩ ⟨ lt , Dominates-trans ys prf lt ⟩
  ... | no ¬lt = y ∷ insert x ys ⟨ Dominates-insert ys (¬x≤y→y≤x ¬lt) prf ⟩

  Dominates-insert : ∀ {n x y} → (ys : SortedVec n) → y ≤ x → ys Dominates y → (insert x ys) Dominates y
  Dominates-insert {zero} {x} []                y≤x dom = y≤x , lift tt
  Dominates-insert {suc n} {x} (z ∷ zs ⟨ prf ⟩) y≤x (y≤z , zsDomy) with x ≤? z
  ... | yes lt = y≤x , y≤z , zsDomy
  ... | no ¬lt = y≤z , Dominates-insert zs y≤x zsDomy

[_] : Carrier → SortedVec 1
[ x ] = x ∷ [] ⟨ lift tt ⟩

tail : ∀ {n} → SortedVec (ℕ.suc n) → SortedVec n
tail (x ∷ xs ⟨ prf ⟩) = xs

head : ∀ {n} → SortedVec (ℕ.suc n) → Carrier
head (x ∷ xs ⟨ prf ⟩) = x

toVec : ∀ {m} → SortedVec m → Vec Carrier m
toVec []               = []′
toVec (x ∷ xs ⟨ prf ⟩) = x ∷′ toVec xs

fromVec : ∀ {m} → Vec Carrier m → SortedVec m
fromVec xs = foldr SortedVec insert [] xs

_++_ : ∀ {m n} → SortedVec m → SortedVec n → SortedVec (m + n)
xs ++ ys = fromVec $ toVec xs ++′ toVec ys

sort : ∀ {m} → Vec Carrier m → Vec Carrier m
sort = toVec ∘ fromVec
