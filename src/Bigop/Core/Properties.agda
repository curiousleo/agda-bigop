module Bigop.Core.Properties where

import Bigop.Core as Core

open import Algebra
open import Data.Product using (proj₁; proj₂)
import Relation.Binary.EqReasoning as EqR

module Fold {c ℓ} (M : Monoid c ℓ) where

  open import Data.List
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
  open P.≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)

  open Monoid M renaming (Carrier to R)
  open Core.Fold M using (fold)
  open EqR setoid

  reducebig : ∀ {i} {I : Set i} → (I → R) → List I → R
  reducebig f = foldr (λ i acc → f i ∙ acc) ε

  equivalent : ∀ {i} {I : Set i} → (f : I → R) → (is : List I) →
               reducebig f is ≡ fold f is
  equivalent f [] = P.refl
  equivalent f (i ∷ is) = start
    f i ∙ reducebig f is
      ≣⟨ P.cong (_∙_ (f i)) (equivalent f is) ⟩
    f i ∙ fold f is □

  foldr≡foldl : (xs : List R) → foldr _∙_ ε xs ≈ foldl _∙_ ε xs
  foldr≡foldl [] = refl
  foldr≡foldl (x ∷ xs) = begin
    x ∙ foldr _∙_ ε xs
      ≈⟨ ∙-cong refl (foldr≡foldl xs) ⟩
    x ∙ foldl _∙_ ε xs
      ≈⟨ foldl-step x xs ⟩
    foldl _∙_ (ε ∙ x) xs ∎
    where
      foldl-cong : ∀ x y xs → x ≈ y → foldl _∙_ x xs ≈ foldl _∙_ y xs
      foldl-cong x y []       x≈y = x≈y
      foldl-cong x y (z ∷ zs) x≈y = foldl-cong (x ∙ z) (y ∙ z) zs (∙-cong x≈y refl)

      foldl-step : ∀ x xs → x ∙ foldl _∙_ ε xs ≈ foldl _∙_ (ε ∙ x) xs
      foldl-step x [] = begin
        x ∙ ε  ≈⟨ proj₂ identity x ⟩
        x      ≈⟨ sym (proj₁ identity x) ⟩
        ε ∙ x  ∎
      foldl-step x (y ∷ ys) = begin
        x ∙ foldl _∙_ (ε ∙ y) ys    ≈⟨ ∙-cong refl (sym (foldl-step y ys)) ⟩
        x ∙ (y ∙ foldl _∙_ ε ys)    ≈⟨ sym (assoc x y _) ⟩
        (x ∙ y) ∙ foldl _∙_ ε ys    ≈⟨ foldl-step (x ∙ y) ys ⟩
        foldl _∙_ (ε ∙ (x ∙ y)) ys  ≈⟨ foldl-cong (ε ∙ (x ∙ y)) (ε ∙ x ∙ y) ys
                                                  (sym (assoc ε x y)) ⟩
        foldl _∙_ (ε ∙ x ∙ y) ys    ∎
