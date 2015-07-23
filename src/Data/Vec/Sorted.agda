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
  hiding (_≤_; _≤?_; total; _≟_)
import Data.Vec as V
open V
  using (Vec; foldr)
  renaming ([] to []′; _∷_ to _∷′_; _++_ to _++′_)

open import Function

open import Relation.Binary.PropositionalEquality
  hiding (isEquivalence; [_])

open import Relation.Nullary

open DecTotalOrder totalOrder
  renaming (trans to ≤-trans; refl to ≤-refl)

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
  x ≼ (y ∷ ys ⟨ prf ⟩) = (x ≤ y) × (x ≼ ys)

≼-decidable : ∀ {n} → Decidable (_≼_ {n})
≼-decidable x []                = yes ∘ lift $ tt
≼-decidable x (y ∷ ys ⟨ y≼ys ⟩) with x ≤? y | ≼-decidable x ys
... | yes lt | yes plt = yes (lt , plt)
... | yes lt | no ¬plt = no $ ¬plt ∘ proj₂
... | no ¬lt | yes plt = no $ ¬lt ∘ proj₁
... | no ¬lt | no ¬plt = no $ ¬plt ∘ proj₂

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

data _∈_ (x : Carrier) : ∀ {n} → SortedVec n → Set (ℓ₁ ⊔ a ⊔ ℓ₂) where
  here  : ∀ {n} → (xs : SortedVec n) → ∀ prf → x ∈ (x ∷ xs ⟨ prf ⟩)
  there : ∀ {n} → (y : Carrier) → (ys : SortedVec n) → ∀ prf → x ∈ ys → x ∈ (y ∷ ys ⟨ prf ⟩)

_++_ : ∀ {m n} → SortedVec m → SortedVec n → SortedVec (m + n)
[]                ++ ys = ys
(x ∷ xs ⟨ x≼xs ⟩) ++ ys = insert x (xs ++ ys)

insert-∈¹ : ∀ {m} → (x : Carrier) → (xs : SortedVec m) → x ∈ insert x xs
insert-∈¹ x []                = here [] (lift tt)
insert-∈¹ x (y ∷ ys ⟨ y≼ys ⟩) with x ≤? y
... | yes lt = here (y ∷ ys ⟨ y≼ys ⟩) (lt , ≼-trans ys y≼ys lt)
... | no ¬lt = there y (insert x ys) (≼-insert ys (¬x≤y→y≤x ¬lt) y≼ys) $ insert-∈¹ x ys

∈-singleton : (x y : Carrier) → ∀ prf → x ∈ (y ∷ [] ⟨ prf ⟩) → x ≡ y
∈-singleton x .x prf (here .[] .prf)        = refl
∈-singleton x y  prf (there .y .[] .prf ())

∷-∈ : ∀ {m} → (x y : Carrier) → (ys : SortedVec m) → ∀ prf → x ∈ (y ∷ ys ⟨ prf ⟩) → (x ≡ y) ⊎ (x ∈ ys)
∷-∈ x y []                 prf x∈ys                                    = inj₁ $ ∈-singleton x y prf x∈ys
∷-∈ y .y (z ∷ zs ⟨ y≼ys ⟩) prf (here  .(z ∷ zs ⟨ y≼ys ⟩) .prf)         = inj₁ refl
∷-∈ x y  (z ∷ zs ⟨ y≼ys ⟩) prf (there .y .(z ∷ zs ⟨ y≼ys ⟩) .prf x∈ys) with ∷-∈ x z zs y≼ys x∈ys
... | inj₁  x≡y rewrite x≡y = inj₂ $ here zs y≼ys
... | inj₂ x∈zs = inj₂ x∈ys

insert-∈² : ∀ {m} → (x y : Carrier) → (xs : SortedVec m) → x ∈ xs → x ∈ insert y xs
insert-∈² x y []                ()
insert-∈² x y (z ∷ zs ⟨ z≼zs ⟩) x∈xs with y ≤? z | ∷-∈ x z zs z≼zs x∈xs
... | yes lt | q = there y (z ∷ zs ⟨ z≼zs ⟩) (lt , ≼-trans zs z≼zs lt) x∈xs
... | no ¬lt | inj₁ x≡z  rewrite x≡z = here (insert y zs) $ ≼-insert zs (¬x≤y→y≤x ¬lt) z≼zs
... | no ¬lt | inj₂ x∈zs = there z (insert y zs) (≼-insert zs (¬x≤y→y≤x ¬lt) z≼zs) $ insert-∈² x y zs x∈zs

++-∈ : ∀ {m n} → (x : Carrier) → (xs : SortedVec m) → (ys : SortedVec n) → (x ∈ xs) ⊎ (x ∈ ys) → x ∈ (xs ++ ys)
++-∈ x [] ys (inj₁ ())
++-∈ x [] ys (inj₂ x∈ys) = x∈ys
++-∈ x (y ∷ xs ⟨ y≼ys ⟩) ys (inj₁ x₁) with ∷-∈ x y xs y≼ys x₁
... | inj₁ x≡y  rewrite x≡y = insert-∈¹ y (xs ++ ys)
... | inj₂ x∈xs = insert-∈² x y (xs ++ ys) (++-∈ x xs ys (inj₁ x∈xs))
++-∈ x (y ∷ xs ⟨ y≼ys ⟩) ys (inj₂ y₁) = insert-∈² x y (xs ++ ys) (++-∈ x xs ys (inj₂ y₁))

fromVec : ∀ {m} → Vec Carrier m → SortedVec m
fromVec = foldr SortedVec insert []

toVec : ∀ {m} → SortedVec m → Vec Carrier m
toVec []               = []′
toVec (x ∷ xs ⟨ prf ⟩) = x ∷′ toVec xs

sort : ∀ {m} → Vec Carrier m → Vec Carrier m
sort = toVec ∘ fromVec

fromVec-∈¹ : ∀ {m} x (xs : Vec Carrier m) → x V.∈ xs → x ∈ (fromVec xs)
fromVec-∈¹ x []′        ()
fromVec-∈¹ x (.x ∷′ xs) V.here         = insert-∈¹ x (fromVec xs)
fromVec-∈¹ x (x′ ∷′ xs) (V.there x∈xs) = insert-∈² x x′ (fromVec xs) (fromVec-∈¹ x xs x∈xs)

postulate
  -- fromVec-∈² : ∀ {m} {x} {xs : Vec Carrier m} → x ∈ (fromVec xs) → x V.∈ xs
  fromVec-∉¹ : ∀ {m} {x} {xs : Vec Carrier m} → ¬ x V.∈ xs → ¬ (x ∈ (fromVec xs))