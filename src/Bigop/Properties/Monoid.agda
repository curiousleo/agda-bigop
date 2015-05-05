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
  f y ∙ fold f (ys ∷ʳ x)   ≈⟨ refl ⟨ ∙-cong ⟩ last f x ys ⟩
  f y ∙ (fold f ys ∙ f x)  ≈⟨ sym $ assoc _ _ _ ⟩
  (f y ∙ fold f ys) ∙ f x  ∎

identity : ∀ {i} {I : Set i} (xs : List I) → fold (const ε) xs ≈ ε
identity []       = refl
identity (x ∷ xs) = trans (proj₁ ident _) (identity xs)

map : ∀ {i j} {I : Set i} {J : Set j} {f : I → R} (g : J → R) (h : I → J) →
      (∀ x → f x ≈ g (h x)) → (is : List I) →
      fold f is ≈ fold g (L.map h is)
map g h fx≈ghx [] = refl
map {f = f} g h fx≈ghx (x ∷ xs) = begin
  f x     ∙ (crush ∘ L.map f) xs              ≈⟨ fx≈ghx x ⟨ ∙-cong ⟩ map g h fx≈ghx xs ⟩
  g (h x) ∙ (crush ∘ (L.map g ∘ L.map h)) xs  ∎

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
cong {f = f} {g} (x ∷ xs) P.refl fx≈gx = begin
  f x ∙ fold f xs  ≈⟨ fx≈gx x ⟨ ∙-cong ⟩ cong xs P.refl fx≈gx ⟩
  g x ∙ fold g xs  ∎

open import Bigop.Filter

cong-P : ∀ {i ℓ} {I : Set i} {f g : I → R} {P : Pred I ℓ} (is : List I)
         (p : Decidable P) →
         (∀ i → (P i) → f i ≈ g i) → fold f (is ∥ p) ≈ fold g (is ∥ p)
cong-P                 []       _ _  = refl
cong-P {f = f} {g} {P} (x ∷ xs) p eq = begin
  fold f (x ∷ xs ∥ p)  ≈⌊ x ∈ p ⌋⟨ case-p ⟩⟨ case-¬p ⟩
  fold g (x ∷ xs ∥ p)  ∎
  where
    open import Bigop.Filter.PredicateReasoning
    open import Relation.Nullary
    open import Relation.Nullary.Decidable
    open import Bigop.Ordinals.Properties

    case-p : P x → fold f (x ∷ xs ∥ p) ≈ fold g (x ∷ xs ∥ p)
    case-p px = begin
      fold f (x ∷ xs ∥ p)    ≡⟨ P.cong (fold f) (head-yes x xs p px) ⟩
      f x ∙ fold f (xs ∥ p)  ≈⟨ ∙-cong (eq x px) (cong-P xs p eq) ⟩
      g x ∙ fold g (xs ∥ p)  ≡⟨ P.cong (fold g) (P.sym $ head-yes x xs p px) ⟩
      fold g (x ∷ xs ∥ p)    ∎

    case-¬p : ¬ P x → fold f (x ∷ xs ∥ p) ≈ fold g (x ∷ xs ∥ p)
    case-¬p ¬px = begin
      fold f (x ∷ xs ∥ p)  ≡⟨ P.cong (fold f) (head-no x xs p ¬px) ⟩
      fold f (xs ∥ p)      ≈⟨ cong-P xs p eq ⟩
      fold g (xs ∥ p)      ≡⟨ P.cong (fold g) (P.sym $ head-no x xs p ¬px) ⟩
      fold g (x ∷ xs ∥ p)  ∎
