open import Algebra

module Bigop.Properties.Monoid {c ℓ} (M : Monoid c ℓ) where

open import Bigop.Core
-- open import Bigop.Filter

open import Data.List.Base as L hiding (map)
open import Data.Product hiding (map)
open import Function
open import Relation.Unary

open Monoid M renaming (Carrier to R; identity to ident)
open import Relation.Binary.EqReasoning setoid

open Fold M

last : ∀ {i} {I : Set i} (f : I → R) (x : I) (xs : List I) →
         fold f (xs ∷ʳ x) ≈ fold f xs ∙ f x
last f x [] = begin
  f x ∙ ε  ≈⟨ proj₂ ident _ ⟩
  f x      ≈⟨ sym $ proj₁ ident _ ⟩
  ε ∙ f x  ∎
last f x (y ∷ ys) = begin
  f y ∙ fold f (ys ∷ʳ x)   ≈⟨ ∙-cong refl (last f x ys) ⟩
  f y ∙ (fold f ys ∙ f x)  ≈⟨ sym $ assoc _ _ _ ⟩
  (f y ∙ fold f ys) ∙ f x  ∎

identity : ∀ {i} {I : Set i} (xs : List I) → fold (const ε) xs ≈ ε
identity []       = refl
identity (x ∷ xs) = trans (proj₁ ident _) (identity xs)

map : ∀ {i j} {I : Set i} {J : Set j} {f : I → R} {g : J → R} (h : I → J) →
      (∀ x → f x ≈ g (h x)) → (is : List I) →
      fold f is ≈ fold g (L.map h is)
map             h f≗gh []       = refl
map {f = f} {g} h f≗gh (i ∷ is) = begin
  f i ∙ fold f is
    ≈⟨ f≗gh i ⟨ ∙-cong ⟩ map {f = f} {g} h f≗gh is ⟩
  g (h i) ∙ fold g (L.map h is) ∎

join : ∀ {i} → {I : Set i} (f : I → R) (xs : List I) (ys : List I) →
       fold f xs ∙ fold f ys ≈ fold f (xs ++ ys)
join f []       ys = proj₁ ident _
join f (x ∷ xs) ys = begin
  (f x ∙  fold f xs) ∙ fold f ys   ≈⟨ assoc _ _ _ ⟩
   f x ∙ (fold f xs  ∙ fold f ys)  ≈⟨ ∙-cong refl (join f xs ys) ⟩
   f x ∙  fold f (xs ++ ys)        ∎

import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

cong : ∀ {i} {I : Set i} {f g : I → R} (is : List I) {js : List I} →
       is ≡ js → (∀ x → f x ≈ g x) → fold f is ≈ fold g js
cong             []       P.refl fx≈gx = refl
cong {f = f} {g} (i ∷ is) P.refl fx≈gx = begin
  f i ∙ fold f is
    ≈⟨ ∙-cong (fx≈gx i) (cong is P.refl fx≈gx) ⟩
  g i ∙ fold g is ∎

open import Bigop.Filter

cong-P : ∀ {i ℓ} {I : Set i} {f g : I → R} {P : Pred I ℓ} (is : List I)
         (p : Decidable P) →
         (∀ i → (P i) → f i ≈ g i) → fold f (is ∥ p) ≈ fold g (is ∥ p)
cong-P                 []       _ _  = refl
cong-P {f = f} {g} {P} (i ∷ is) p eq = begin
  fold f (i ∷ is ∥ p)
    ≈⌊ i ∈ p ⌋⟨ (λ pi →

    begin
      fold f (i ∷ is ∥ p)    ≡⟨ P.cong (fold f) (head-yes i is p pi) ⟩
      f i ∙ fold f (is ∥ p)  ≈⟨ ∙-cong (eq i pi) (cong-P is p eq) ⟩
      g i ∙ fold g (is ∥ p)  ≡⟨ P.cong (fold g) (P.sym $ head-yes i is p pi) ⟩
      fold g (i ∷ is ∥ p)    ∎
    )

    ⟩⟨ (λ ¬pi →

    begin
      fold f (i ∷ is ∥ p)  ≡⟨ P.cong (fold f) (head-no i is p ¬pi) ⟩
      fold f (is ∥ p)      ≈⟨ cong-P is p eq ⟩
      fold g (is ∥ p)      ≡⟨ P.cong (fold g) (P.sym $ head-no i is p ¬pi) ⟩
      fold g (i ∷ is ∥ p)  ∎
    )⟩

  fold g (i ∷ is ∥ p) ∎
  where
    open import Bigop.Filter.PredicateReasoning
    open import Relation.Nullary
    open import Relation.Nullary.Decidable
    open import Bigop.Ordinals.Properties
