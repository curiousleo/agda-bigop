open import Relation.Binary

module Data.Vec.Sorted
  {a ℓ₁ ℓ₂}
  (totalOrder : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Level

open import Data.Empty
open import Data.Fin
  using (Fin; zero; suc)
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
... | inj₁ p = ⊥-elim ∘ prf $ p
... | inj₂ p = p

mutual
 
  data SortedVec : ℕ → Set (ℓ₂ ⊔ a) where
    []     : SortedVec 0
    _∷_⟨_⟩ : ∀ {n} → (y : Carrier) → (ys : SortedVec n) → (y≼ys : y ≼ ys) → SortedVec (ℕ.suc n)

  _≼_ : ∀ {n} → Carrier → SortedVec n → Set ℓ₂
  x ≼ []               = Lift ⊤
  x ≼ (y ∷ ys ⟨ prf ⟩) = x ≤ y × x ≼ ys

≼-trans : ∀ {n y x} → (xs : SortedVec n) → x ≼ xs → y ≤ x → y ≼ xs
≼-trans []               xsDomx         y≤x = lift tt
≼-trans (z ∷ zs ⟨ prf ⟩) (x≤z , zsDomx) y≤x = ≤-trans y≤x x≤z , ≼-trans zs zsDomx y≤x

mutual

  insert : ∀ {n} → Carrier → SortedVec n → SortedVec (ℕ.suc n)
  insert x []               = x ∷ [] ⟨ lift tt ⟩
  insert x (y ∷ ys ⟨ prf ⟩) with x ≤? y
  ... | yes lt = x ∷ y ∷ ys ⟨ prf ⟩ ⟨ lt , ≼-trans ys prf lt ⟩
  ... | no ¬lt = y ∷ insert x ys ⟨ ≼-insert ys (¬x≤y→y≤x ¬lt) prf ⟩

  ≼-insert : ∀ {n x y} → (ys : SortedVec n) → y ≤ x → y ≼ ys → y ≼ (insert x ys)
  ≼-insert {zero} {x} []                y≤x dom = y≤x , lift tt
  ≼-insert {suc n} {x} (z ∷ zs ⟨ prf ⟩) y≤x (y≤z , zsDomy) with x ≤? z
  ... | yes lt = y≤x , y≤z , zsDomy
  ... | no ¬lt = y≤z , ≼-insert zs y≤x zsDomy

[_] : Carrier → SortedVec 1
[ x ] = x ∷ [] ⟨ lift tt ⟩

tail : ∀ {n} → SortedVec (ℕ.suc n) → SortedVec n
tail (x ∷ xs ⟨ prf ⟩) = xs

mutual

  init : ∀ {n} → SortedVec (ℕ.suc n) → SortedVec n
  init (x ∷ []                ⟨ prf₁ ⟩) = []
  init (x ∷ xs ∷ xss ⟨ prf₁ ⟩ ⟨ prf₂ ⟩) = x ∷ init (xs ∷ xss ⟨ prf₁ ⟩) ⟨ ≼-init (xs ∷ xss ⟨ prf₁ ⟩) prf₂ ⟩

  ≼-init : ∀ {x n} → (xs : SortedVec (ℕ.suc n)) → x ≼ xs → x ≼ (init xs)
  ≼-init (x₁ ∷ [] ⟨ prf₁ ⟩)             prf₂ = lift tt
  ≼-init (x₁ ∷ x₂ ∷ xs ⟨ x₃ ⟩ ⟨ prf₁ ⟩) prf₂ = proj₁ prf₂ , ≼-init (x₂ ∷ xs ⟨ x₃ ⟩) (proj₂ prf₂)

head : ∀ {n} → SortedVec (ℕ.suc n) → Carrier
head (x ∷ xs ⟨ prf ⟩) = x

mutual

  take : ∀ m {n} → SortedVec (m + n) → SortedVec m
  take zero    xs                = []
  take (suc m) (x ∷ xs ⟨ x≼xs ⟩) = x ∷ take m xs ⟨ ≼-take m x xs x≼xs ⟩

  ≼-take : ∀ m {n} → (x : Carrier) → (xs : SortedVec (m + n)) → x ≼ xs →
           x ≼ take m xs
  ≼-take zero    x xs                x≼xs         = lift tt
  ≼-take (suc m) x (y ∷ ys ⟨ y≼ys ⟩) (x≤y , x≼ys) = x≤y , (≼-take m x ys x≼ys)

drop : ∀ m {n} → SortedVec (m + n) → SortedVec n
drop zero    xs                = xs
drop (suc m) (x ∷ xs ⟨ x≼xs ⟩) = drop m xs

splitAt : ∀ m {n} → SortedVec (m + n) → SortedVec m × SortedVec n
splitAt m xs = take m xs , drop m xs

lookup : ∀ {n} → SortedVec n → Fin n → Carrier
lookup []               ()
lookup (x ∷ xs ⟨ prf ⟩) zero     = x
lookup (x ∷ xs ⟨ prf ⟩) (suc ix) = lookup xs ix

toVec : ∀ {m} → SortedVec m → Vec Carrier m
toVec []               = []′
toVec (x ∷ xs ⟨ prf ⟩) = x ∷′ toVec xs

fromVec : ∀ {m} → Vec Carrier m → SortedVec m
fromVec = foldr SortedVec insert []

_++_ : ∀ {m n} → SortedVec m → SortedVec n → SortedVec (m + n)
xs ++ ys = fromVec $ toVec xs ++′ toVec ys

sort : ∀ {m} → Vec Carrier m → Vec Carrier m
sort = toVec ∘ fromVec
