open import Relation.Binary

module Data.List.Sorted
  {a ℓ₁ ℓ₂}
  {A : Set a}
  {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂}
  (isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_)
  where

open import Data.List.Base
open import Data.Product
open import Data.Empty
open import Level
open import Relation.Nullary

open IsStrictTotalOrder isStrictTotalOrder renaming (trans to sto-trans)
open IsEquivalence isEquivalence

_≤_ : Rel A ℓ₂
a ≤ b = ¬ b < a

_≤?_ : ∀ a b → Dec (a ≤ b)
x ≤? y with compare x y
... | tri< a ¬b ¬c = yes ¬c
... | tri≈ ¬a b ¬c = yes ¬c
... | tri> ¬a ¬b c = no (λ z → z c)

<→≤ : ∀ {a b} → a < b → a ≤ b
<→≤ {x} {y} x<y with compare x y
<→≤ x<y | tri< a ¬b ¬c = ¬c
<→≤ x<y | tri≈ ¬a b ¬c = ¬c
<→≤ x<y | tri> ¬a ¬b c = ⊥-elim (¬a x<y)

¬¬<→< : ∀ {a b} → ¬ ¬ a < b → a < b
¬¬<→< {x} {y} ¬¬x<y with x <? y
¬¬<→< ¬¬x<y | yes p = p
¬¬<→< ¬¬x<y | no ¬p = ⊥-elim (¬¬x<y ¬p)

insert : A → List A → List A
insert x [] = [ x ]
insert x (y ∷ ys) with x ≤? y
... | yes _ = x ∷ y ∷ ys
... | no  _ = y ∷ insert x ys

data Sorted : List A → Set (a ⊔ ℓ₂) where
  empty  : Sorted []
  single : ∀ {x} → Sorted [ x ]
  cons   : ∀ {x y ys} (lte : x ≤ y) (sorted : Sorted (y ∷ ys)) → Sorted (x ∷ y ∷ ys)

postulate
  insert-lemma : (x : A) → (xs : List A) → Sorted xs → Sorted (insert x xs)

{-
insert-lemma : (x : A) → (xs : List A) → Sorted xs → Sorted (insert x xs)
insert-lemma x [] empty = single
insert-lemma x (y ∷ []) single with x ≤? y
... | yes lt = cons lt single
... | no ¬lt = cons (<→≤ (¬¬<→< ¬lt)) single
insert-lemma x (y ∷ z ∷ zs) sorted = {!!}
-}

sort : List A → List A
sort = foldr insert []

sort-lemma : (xs : List A) → Sorted (sort xs)
sort-lemma []       = empty
sort-lemma (x ∷ xs) = insert-lemma x (sort xs) (sort-lemma xs)
