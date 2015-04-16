open import Algebra

module Bigop.Properties.Monoid {c ℓ} (M : Monoid c ℓ) where

open import Bigop.Core
-- open import Bigop.Filter

open import Data.List.Base
open import Data.Product hiding (map)
open import Function
open import Relation.Unary
import Relation.Binary.EqReasoning as EqR

open Monoid M renaming (Carrier to R)
open EqR setoid

open Fold M

last : ∀ {i} {I : Set i} (f : I → R) (x : I) (xs : List I) →
         fold f (xs ∷ʳ x) ≈ fold f xs ∙ f x
last f x [] = begin
  f x ∙ ε  ≈⟨ proj₂ identity _ ⟩
  f x      ≈⟨ sym $ proj₁ identity _ ⟩
  ε ∙ f x  ∎
last f x (y ∷ ys) = begin
  f y ∙ fold f (ys ∷ʳ x)   ≈⟨ ∙-cong refl (last f x ys) ⟩
  f y ∙ (fold f ys ∙ f x)  ≈⟨ sym $ assoc _ _ _ ⟩
  (f y ∙ fold f ys) ∙ f x  ∎

shift : ∀ {i} {I : Set i} (f : I → R) (x : I) (xs : List I) →
          f x ≈ ε → fold f (x ∷ xs) ≈ fold f xs
shift f x xs fx≈ε = begin
  f x ∙ fold f xs  ≈⟨ ∙-cong fx≈ε refl ⟩
  ε ∙ fold f xs    ≈⟨ proj₁ identity _ ⟩
  fold f xs        ∎

zero : ∀ {i} {I : Set i} (xs : List I) → fold (const ε) xs ≈ ε
zero [] = refl
zero (x ∷ xs) = trans (proj₁ identity _) (zero xs)

cong′ : ∀ {i} {I : Set i} {f g : I → R} → (∀ x → f x ≈ g x) → (is : List I) →
          fold f is ≈ fold g is
cong′         f≗g []       = refl
cong′ {f = f} {g} f≗g (i ∷ is) = begin
  f i ∙ fold f is
    ≈⟨ f≗g i ⟨ ∙-cong ⟩ cong′ {f = f} {g} f≗g is ⟩
  g i ∙ fold g is ∎

-- cong could be generalised further to f : I → R, g : J → R, h : I → J
cong : ∀ {i} {I : Set i} {f g : I → R} (h : I → I) →
         (∀ x → f x ≈ g (h x)) → (is : List I) →
         fold f is ≈ fold g (map h is)
cong         h f≗gh []       = refl
cong {f = f} {g} h f≗gh (i ∷ is) = begin
  f i ∙ fold f is
    ≈⟨ f≗gh i ⟨ ∙-cong ⟩ cong {f = f} {g} h f≗gh is ⟩
  g (h i) ∙ fold g (map h is) ∎

import Relation.Binary.PropositionalEquality as P

cong″ : ∀ {i} {I : Set i} {f g : I → R} → (∀ x → f x ≈ g x) →
          {is : List I} → {js : List I} → is P.≡ js →
          fold f is ≈ fold g js
cong″ fx≈gx {[]} P.refl = refl
cong″ {f = f} {g} fx≈gx {i ∷ is} P.refl = begin
  f i ∙ fold f is
    ≈⟨ ∙-cong (fx≈gx i) (cong″ fx≈gx (P.refl {x = is})) ⟩
  g i ∙ fold g is ∎

open import Bigop.Filter

postulate
  cong-P : ∀ {i ℓ} {I : Set i} {f g : I → R} {P : Pred I ℓ} (is : List I)
           (p : Decidable P) →
           (∀ i → (P i) → f i ≈ g i) → fold f (is ∥ p) ≈ fold g (is ∥ p)
