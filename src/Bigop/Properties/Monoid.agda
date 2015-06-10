------------------------------------------------------------------------
-- Big operator library
--
-- Equivalences for big operators over a monoid
------------------------------------------------------------------------

open import Algebra

module Bigop.Properties.Monoid {c ℓ} (M : Monoid c ℓ) where

open import Bigop.Core
open import Bigop.Filter

open import Data.List.Base as L hiding (map)
open import Data.List.Any using (here; there; module Membership)
open import Data.Product hiding (map)

open import Function

open Membership using (_∈_)

open Monoid M renaming (Carrier to R; identity to ident)

open import Relation.Binary.EqReasoning setoid
import Relation.Binary.PropositionalEquality as P
open import Relation.Unary hiding (_∈_)

open P using (_≡_)

open Fold M using (crush; fold)

-- List append distributes over big operators
-- (⨁[ i ← is ] f i) ⊕ (⨁[ j ← js ] f j) ≈ ⨁[ i ← is ++ js ] f i

++-distr : ∀ {i} → {I : Set i} (f : I → R) (xs : List I) (ys : List I) →
       fold f xs ∙ fold f ys ≈ fold f (xs ++ ys)
++-distr f []       ys = proj₁ ident _
++-distr f (x ∷ xs) ys = begin
  (f x ∙  fold f xs) ∙ fold f ys   ≈⟨ assoc _ _ _ ⟩
   f x ∙ (fold f xs  ∙ fold f ys)  ≈⟨ ∙-cong refl (++-distr f xs ys) ⟩
   f x ∙  fold f (xs ++ ys)        ∎

-- This lets us extract the last element of the index list
-- ⨁[ i ← js ∷ʳ j ] f i ≈ (⨁[ i ← js ] f i) ⊕ f j

snoc : ∀ {i} {I : Set i} (f : I → R) (x : I) (xs : List I) →
         fold f (xs ∷ʳ x) ≈ fold f xs ∙ f x
snoc f x xs =
  begin
    fold f (xs ∷ʳ x)
      ≈⟨ sym $ ++-distr f xs [ x ] ⟩
    fold f xs ∙ fold f [ x ]
      ≈⟨ ∙-cong refl $ proj₂ ident (f x) ⟩
    fold f xs ∙ f x
  ∎

-- Folding over the identity evaluates to the identity

identity : ∀ {i} {I : Set i} (xs : List I) → fold (const ε) xs ≈ ε
identity []       = refl
identity (x ∷ xs) = trans (proj₁ ident _) (identity xs)

-- Can map over the list of indices if the expressions are equivalent

map : ∀ {i j} {I : Set i} {J : Set j} {f : I → R} (g : J → R) (h : I → J) →
      (∀ x → f x ≈ g (h x)) → (is : List I) →
      fold f is ≈ fold g (L.map h is)
map g h fx≈ghx [] = refl
map {f = f} g h fx≈ghx (x ∷ xs) = begin
  f x     ∙ (crush ∘ L.map f) xs              ≈⟨ fx≈ghx x ⟨ ∙-cong ⟩ map g h fx≈ghx xs ⟩
  g (h x) ∙ (crush ∘ (L.map g ∘ L.map h)) xs  ∎

-- Weaker variant of the above: here the expressions must only be equivalent for
-- indices in the list (instead of any index of that type)

map′ : ∀ {i j} {I : Set i} {J : Set j} {f : I → R} (g : J → R) (h : I → J) →
      (xs : List I) → (∀ x → _∈_ (P.setoid I) x xs → f x ≈ g (h x)) →
      fold f xs ≈ fold g (L.map h xs)
map′ g h [] fx≈ghx = refl
map′ {f = f} g h (x ∷ xs) fx≈ghx = begin
  f x ∙ (crush ∘ L.map f) xs ≈⟨ fx≈ghx x (here P.refl) ⟨ ∙-cong ⟩
                                map′ g h xs (λ x elt → fx≈ghx x (there elt)) ⟩
  g (h x) ∙ (crush ∘ (L.map g ∘ L.map h)) xs ∎

-- Congruence rule for big operators

cong : ∀ {i} {I : Set i} {f g : I → R} (is : List I) {js : List I} →
       is ≡ js → (∀ x → f x ≈ g x) → fold f is ≈ fold g js
cong             []       P.refl fx≈gx = refl
cong {f = f} {g} (x ∷ xs) P.refl fx≈gx = begin
  f x ∙ fold f xs  ≈⟨ fx≈gx x ⟨ ∙-cong ⟩ cong xs P.refl fx≈gx ⟩
  g x ∙ fold g xs  ∎

-- Congruence rule for big operators restricted to indices in the index list

cong′ : ∀ {i} {I : Set i} {f g : I → R} (is : List I) {js : List I} →
       is ≡ js → (∀ x → _∈_ (P.setoid I) x is → f x ≈ g x) → fold f is ≈ fold g js
cong′             []       P.refl fx≈gx = refl
cong′ {f = f} {g} (x ∷ xs) P.refl fx≈gx = begin
  f x ∙ fold f xs  ≈⟨ fx≈gx x (here P.refl) ⟨ ∙-cong ⟩
                      cong′ xs P.refl (λ x elt → fx≈gx x (there elt)) ⟩
  g x ∙ fold g xs  ∎

-- Congruence rule for filtered index lists

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
    open import Bigop.Filter.Properties

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
