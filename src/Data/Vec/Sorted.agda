open import Relation.Binary

module Data.Vec.Sorted
  {a ℓ₁ ℓ₂}
  (A : Set a)
  {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂}
  (isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_)
  where

open import Level

open import Data.Empty
open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Unit
  hiding (_≤_; _≤?_)
open import Data.Vec
  using (Vec; foldr)

open import Function

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)
open import Relation.Nullary

open IsStrictTotalOrder isStrictTotalOrder renaming (trans to sto-trans)
open IsEquivalence isEquivalence hiding (sym)

_≤_ : Rel A ℓ₂
a ≤ b = ¬ b < a

_≤?_ : ∀ a b → Dec (a ≤ b)
x ≤? y with compare x y
... | tri< a ¬b ¬c = yes ¬c
... | tri≈ ¬a b ¬c = yes ¬c
... | tri> ¬a ¬b c = no (λ z → z c)

¬¬<→< : ∀ {a b} → ¬ ¬ a < b → a < b
¬¬<→< {x} {y} ¬¬x<y with x <? y
¬¬<→< ¬¬x<y | yes p = p
¬¬<→< ¬¬x<y | no ¬p = ⊥-elim (¬¬x<y ¬p)

<→≤ : ∀ {a b} → a < b → a ≤ b
<→≤ {x} {y} x<y with compare x y
<→≤ x<y | tri< a ¬b ¬c = ¬c
<→≤ x<y | tri≈ ¬a b ¬c = ¬c
<→≤ x<y | tri> ¬a ¬b c = ⊥-elim (¬a x<y)

≤-refl : Reflexive _≤_
≤-refl x = irrefl (IsEquivalence.refl
                     (IsStrictTotalOrder.isEquivalence isStrictTotalOrder)) x

≤-trans : Transitive _≤_
≤-trans {x} {y} {z} y<x→⊥ z<y→⊥ z<x with compare x y | compare x z | compare y z
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri< a₂ ¬b₁ ¬c₁ | tri< a₃ ¬b₂ ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri< a₂ ¬b₁ ¬c₁ | tri≈ ¬a b ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri< a₂ ¬b₁ ¬c₁ | tri> ¬a ¬b₂ c = z<y→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri< a₁ ¬b ¬c₁ | tri< a₂ ¬b₁ ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri< a₁ ¬b ¬c₁ | tri≈ ¬a₁ b₁ ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri< a₁ ¬b ¬c₁ | tri> ¬a₁ ¬b₁ c = z<y→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri< a₁ ¬b₁ ¬c | tri< a₂ ¬b₂ ¬c₁ = y<x→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri< a₁ ¬b₁ ¬c | tri≈ ¬a₁ b ¬c₁ = y<x→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri< a₁ ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ = z<y→⊥ c₁
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri≈ ¬a b ¬c₁ | tri< a₂ ¬b₁ ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri≈ ¬a b ¬c₁ | tri≈ ¬a₁ b₁ ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri≈ ¬a b ¬c₁ | tri> ¬a₁ ¬b₁ c = z<y→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri≈ ¬a₁ b₁ ¬c₁ | tri< a₁ ¬b ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri≈ ¬a₁ b₁ ¬c₁ | tri≈ ¬a₂ b₂ ¬c₂ = ¬c₁ z<x
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri≈ ¬a₁ b₁ ¬c₁ | tri> ¬a₂ ¬b c = z<y→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c | tri< a₁ ¬b₁ ¬c₁ = y<x→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c | tri≈ ¬a₂ b₁ ¬c₁ = y<x→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c | tri> ¬a₂ ¬b₁ c₁ = z<y→⊥ c₁
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri> ¬a ¬b₁ c | tri< a₂ ¬b₂ ¬c₁ = ¬a (sto-trans a₁ a₂)
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri> ¬a ¬b₁ c | tri≈ ¬a₁ b ¬c₁ = ¬c₁ (sto-trans c a₁)
≤-trans y<x→⊥ z<y→⊥ z<x | tri< a₁ ¬b ¬c | tri> ¬a ¬b₁ c | tri> ¬a₁ ¬b₂ c₁ = z<y→⊥ (sto-trans z<x a₁)
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c | tri< a₁ ¬b₁ ¬c₁ = y<x→⊥ (sto-trans a₁ c)
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c | tri≈ ¬a₂ b₁ ¬c₁ = ¬b (trans b b₁)
≤-trans y<x→⊥ z<y→⊥ z<x | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c | tri> ¬a₂ ¬b₁ c₁ = z<y→⊥ c₁
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | tri< a₁ ¬b₂ ¬c = y<x→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | tri≈ ¬a₂ b ¬c = y<x→⊥ c
≤-trans y<x→⊥ z<y→⊥ z<x | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | tri> ¬a₂ ¬b₂ c₂ = z<y→⊥ c₂

mutual
 
  data SortedVec : ℕ → Set (ℓ₂ ⊔ a) where
    []     : SortedVec 0
    _∷_⟨_⟩ : ∀ {n} → (x : A) → (xs : SortedVec n) → xs Dominates x → SortedVec (ℕ.suc n)

  _Dominates_ : ∀ {n} → SortedVec n → A → Set ℓ₂
  []               Dominates x = Lift ⊤
  (y ∷ ys ⟨ prf ⟩) Dominates x = (x ≤ y) × (ys Dominates x)

Dominates-trans : ∀ {n y x} → (xs : SortedVec n) → xs Dominates x → y ≤ x → xs Dominates y
Dominates-trans []               xsDomx         y≤x = lift tt
Dominates-trans (z ∷ zs ⟨ prf ⟩) (x≤z , zsDomx) y≤x = ≤-trans y≤x x≤z , Dominates-trans zs zsDomx y≤x

mutual

  insert : ∀ {n} → A → SortedVec n → SortedVec (ℕ.suc n)
  insert x []               = x ∷ [] ⟨ lift tt ⟩
  insert x (y ∷ ys ⟨ prf ⟩) with x ≤? y
  ... | yes lt = x ∷ y ∷ ys ⟨ prf ⟩ ⟨ lt , Dominates-trans ys prf lt ⟩
  ... | no ¬lt = y ∷ insert x ys ⟨ Dominates-insert ys (¬¬<→< ¬lt) prf ⟩

  Dominates-insert : ∀ {n x y} → (ys : SortedVec n) → y < x → ys Dominates y → (insert x ys) Dominates y
  Dominates-insert {zero} {x} []               y<x dom = <→≤ y<x , lift tt
  Dominates-insert {suc n} {x} (z ∷ zs ⟨ prf ⟩) y<x (y≤z , zsDomy) with x ≤? z
  ... | yes lt = <→≤ y<x , y≤z , zsDomy
  ... | no ¬lt = y≤z , Dominates-insert zs y<x zsDomy

tail : ∀ {n} → (xs : SortedVec (ℕ.suc n)) → SortedVec n
tail (x ∷ xs ⟨ prf ⟩) = xs

head : ∀ {n} → (xs : SortedVec (ℕ.suc n)) → ∃ λ x → (tail xs) Dominates x
head (x ∷ xs ⟨ prf ⟩) = x , prf

{-
massage : ∀ {m n} → m ≡ n → SortedVec m → SortedVec n
massage refl xs = xs

Dominates-massage : ∀ {m n x} → (p : m ≡ n) → (xs : SortedVec m) → xs Dominates x → (massage p xs) Dominates x
Dominates-massage {m} {.m} {x} refl xs xsDomx = xsDomx

mutual

  merge : ∀ {m n} → (xs : SortedVec m) → (ys : SortedVec n) →
    SortedVec (m + n)
  merge {zero}  {n}     []                ys                = ys
  merge {m}     {zero}  xs                []                = massage (sym $ +-right-identity m) xs
  merge {suc m} {suc n} (x ∷ xs ⟨ prf₁ ⟩) (y ∷ ys ⟨ prf₂ ⟩) with x ≤? y
  ... | yes lt = massage (sym $ +-suc (Data.Nat.suc m) n) (x ∷ y ∷ merge xs ys ⟨ Dominates-merge¹ {!xs!} ys (Dominates-trans {!!} {!prf₂!} lt) prf₂ ≤-refl ⟩ ⟨ lt , Dominates-merge¹ xs ys prf₁ prf₂ lt ⟩)
  ... | no ¬lt = massage (sym $ +-suc (Data.Nat.suc m) n) (y ∷ x ∷ merge xs ys ⟨ Dominates-merge⁴ xs ys prf₁ prf₂ (<→≤ (¬¬<→< ¬lt)) ⟩ ⟨ <→≤ (¬¬<→< ¬lt) , Dominates-merge³ xs ys prf₁ prf₂ (<→≤ (¬¬<→< ¬lt)) ⟩)

  Dominates-merge¹ : ∀ {x y m n} → (xs : SortedVec m) → (ys : SortedVec n) → xs Dominates x → ys Dominates y → x ≤ y → (merge xs ys) Dominates x
  Dominates-merge¹ {w} {z} {zero}  {zero}  []               []                xsDomx ysDomy w≤z = lift tt
  Dominates-merge¹ {w} {z} {zero}  {suc n} []               (y ∷ ys ⟨ prf₂ ⟩) xsDomx ysDomy w≤z = ≤-trans w≤z (proj₁ ysDomy) , Dominates-trans ys (proj₂ ysDomy) w≤z
  Dominates-merge¹ {w} {z} {suc m} {zero}  (x ∷ xs ⟨ prf ⟩) []                xsDomx ysDomy w≤z = Dominates-massage (sym (cong Data.Nat.suc (+-right-identity m))) (x ∷ xs ⟨ prf ⟩) xsDomx
  Dominates-merge¹ {w} {z} {suc m} {suc n} (x ∷ xs ⟨ prf ⟩) (y ∷ ys ⟨ prf₂ ⟩) xsDomx ysDomy w≤z with x ≤? y
  ... | yes lt = Dominates-massage (sym $ cong Data.Nat.suc (+-suc m n)) (x ∷ y ∷ merge xs ys ⟨ Dominates-merge² xs ys prf prf₂ lt ⟩ ⟨ lt , Dominates-merge¹ xs ys prf prf₂ lt ⟩) (proj₁ xsDomx , (≤-trans (proj₁ xsDomx) lt , Dominates-merge¹ xs ys (proj₂ xsDomx) (proj₂ ysDomy) w≤z))
  ... | no ¬lt = Dominates-massage (sym $ cong Data.Nat.suc (+-suc m n)) ((y ∷ x ∷ merge xs ys ⟨ Dominates-merge⁴ xs ys prf prf₂ (<→≤ (¬¬<→< ¬lt)) ⟩ ⟨ <→≤ (¬¬<→< ¬lt) , Dominates-merge³ xs ys prf prf₂ (<→≤ (¬¬<→< ¬lt)) ⟩)) (≤-trans w≤z (proj₁ ysDomy) , (proj₁ xsDomx , Dominates-merge¹ xs ys (proj₂ xsDomx) (proj₂ ysDomy) w≤z))

  Dominates-merge² : ∀ {x y m n} → (xs : SortedVec m) → (ys : SortedVec n) → xs Dominates x → ys Dominates y → x ≤ y → (merge xs ys) Dominates y
  Dominates-merge² {w} {z} {zero}  {zero}  []                []                xsDomx ysDomy w≤z = lift tt
  Dominates-merge² {w} {z} {zero}  {suc n} []                (y ∷ ys ⟨ prf₂ ⟩) xsDomx ysDomy w≤z = ysDomy
  Dominates-merge² {w} {z} {suc m} {zero}  (x ∷ xs ⟨ prf₁ ⟩) []                xsDomx ysDomy w≤z = Dominates-massage {!!} (x ∷ xs ⟨ prf₁ ⟩) {!xsDomx!}
  Dominates-merge² {w} {z} {suc m} {suc n} (x ∷ xs ⟨ prf₁ ⟩) (y ∷ ys ⟨ prf₂ ⟩) xsDomx ysDomy w≤z = {!!}

  Dominates-merge³ : ∀ {x y m n} → (xs : SortedVec m) → (ys : SortedVec n) → xs Dominates y → ys Dominates x → x ≤ y → (merge xs ys) Dominates x
  Dominates-merge³ xs ys xsDomx ysDomy x≤y = {!!}

  Dominates-merge⁴ : ∀ {x y m n} → (xs : SortedVec m) → (ys : SortedVec n) → xs Dominates y → ys Dominates x → x ≤ y → (merge xs ys) Dominates y
  Dominates-merge⁴ xs ys xsDomx ysDomy x≤y = {!!}
-}

sort : ∀ {n} → (xs : Vec A n) → SortedVec n
sort xs = Data.Vec.foldr SortedVec insert [] xs
