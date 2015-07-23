------------------------------------------------------------------------
-- Big operator library
--
-- Equivalences for big operators over a commutative monoid
------------------------------------------------------------------------

module Bigop.Properties.CommutativeMonoid where

open import Algebra

open import Bigop.Core

open import Bigop.Filter using (_∥_; ∁′)
open import Bigop.Filter.PredicateReasoning
open import Bigop.Filter.Properties

import Bigop.Properties.Monoid as MonoidProps

open import Data.List.Base
open import Data.List.Properties
open import Data.Product hiding (map; swap)

open import Function

open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary
import Relation.Binary.PropositionalEquality as P

module RequiresCommutativeMonoid {c ℓ} (M : CommutativeMonoid c ℓ) where

  open CommutativeMonoid M renaming (identity to ident; comm to ∙-comm)
  open Fold monoid
  open MonoidProps {c} {ℓ} monoid public

  open import Relation.Binary.EqReasoning setoid

  -- We can reverse the index list without changing the result of the big
  -- operator expression: ⨁[ i ← is ] f i ≈ ⨁[ i ← reverse is ] f i

  fold-reverse : ∀ {ℓ} {I : Set ℓ} (f : I → Carrier) (is : List I) → fold f is ≈ fold f (reverse is)
  fold-reverse {ℓ} {I} f []       = refl
  fold-reverse {ℓ} {I} f (i ∷ is) = begin
    f i ∙ fold f is
      ≈⟨ ∙-comm _ _ ⟩
    fold f is ∙ f i
      ≈⟨ ∙-cong (fold-reverse f is) refl ⟩
    fold f (reverse is) ∙ f i
      ≈⟨ sym (snoc f i (reverse is)) ⟩
    fold f (reverse is ∷ʳ i)
      ≈⟨ cong (reverse is ∷ʳ i) (P.sym $ reverse-++-commute [ i ] is) (λ x → refl) ⟩
    fold f (reverse (i ∷ is)) ∎

  -- The small operator distributes over its big operator
  -- (⨁[ i ← is ] f i) ⊕ (⨁[ i ← is ] g i) ≈ ⨁[ i ← is ] f i ⊕ g i

  ∙-distr : ∀ {i} {I : Set i} (f g : I → Carrier) (is : List I) →
    fold f is ∙ fold g is ≈ fold (λ i → f i ∙ g i) is
  ∙-distr f g [] = proj₁ ident _
  ∙-distr f g (i ∷ is) = begin
    (f i ∙ fold f is) ∙ (g i ∙ fold g is)
      ≈⟨ assoc (f i) (fold f is) (g i ∙ fold g is) ⟩
    f i ∙ (fold f is ∙ (g i ∙ fold g is))
      ≈⟨ refl {f i} ⟨ ∙-cong ⟩ lemma ⟩
    f i ∙ (g i ∙ fold (λ i → f i ∙ g i) is)
      ≈⟨ sym (assoc (f i) (g i) (fold (λ i → f i ∙ g i) is)) ⟩
    (f i ∙ g i) ∙ fold (λ i → f i ∙ g i) is ∎
    where
      lemma : fold f is ∙ (g i ∙ fold g is) ≈
              g i ∙ fold (λ i → f i ∙ g i) is
      lemma = begin
        fold f is ∙ (g i ∙ fold g is)
          ≈⟨ sym (assoc (fold f is) (g i) (fold g is)) ⟩
        (fold f is ∙ g i) ∙ fold g is
          ≈⟨ ∙-comm (fold f is) (g i) ⟨ ∙-cong ⟩ refl ⟩
        (g i ∙ fold f is) ∙ fold g is
          ≈⟨ assoc (g i) (fold f is) (fold g is) ⟩
        g i ∙ (fold f is ∙ fold g is)
          ≈⟨ (refl {g i}) ⟨ ∙-cong ⟩ ∙-distr f g is ⟩
        g i ∙ fold (λ i → f i ∙ g i) is ∎

  -- Swapping the order of big operators is allowed
  -- ⨁[ j ← js ] (⨁[ i ← is ] f j i) ≈ ⨁[ i ← is ] (⨁[ j ← js ] f j i)

  comm : ∀ {i j} {I : Set i} {J : Set j} (f : J → I → Carrier)
       (js : List J) (is : List I) →
         fold (λ j → fold (f j) is) js ≈ fold (λ i → fold (flip f i) js) is
  comm f [] ys = sym (identity ys)
  comm f xs [] = identity xs
  comm f (x ∷ xs) ys = begin
    fold (f x) ys ∙ fold (λ j → fold (f j) ys) xs
      ≈⟨ refl {fold (f x) ys} ⟨ ∙-cong ⟩ comm f xs ys ⟩
    fold (f x) ys ∙ fold (λ i → fold (flip f i) xs) ys
      ≈⟨ ∙-distr (f x) (λ i → fold (flip f i) xs) ys ⟩
    fold (λ i → f x i ∙ fold (flip f i) xs) ys ∎

  ------------------------------------------------------------------------
  -- Splitting the index list using a decidable predicate
  
  split-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → (f : I → Carrier) (i : I) (is : List I)
    (p : Decidable P) → P i → f i ∙ (fold f (is ∥ p) ∙ fold f (is ∥ ∁′ p))
                    ≈ fold f ((i ∷ is) ∥ p) ∙ fold f ((i ∷ is) ∥ ∁′ p)
  split-yes f i is p pi = begin
    f i ∙ (fold f (is ∥ p) ∙ fold f (is ∥ ∁′ p))
      ≈⟨ sym (assoc _ _ _) ⟩
    fold f (i ∷ (is ∥ p)) ∙ fold f (is ∥ ∁′ p)
      ≡⟨ P.sym $ P.cong₂ _∙_ (P.cong (fold f) (head-yes i is p pi))
                         (P.cong (fold f) (head-∁-yes i is p pi)) ⟩
    fold f ((i ∷ is) ∥ p) ∙ fold f ((i ∷ is) ∥ ∁′ p) ∎

  split-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → (f : I → Carrier) (i : I) (is : List I)
    (p : Decidable P) → ¬ P i → f i ∙ (fold f (is ∥ p) ∙ fold f (is ∥ ∁′ p))
                     ≈ fold f ((i ∷ is) ∥ p) ∙ fold f ((i ∷ is) ∥ ∁′ p)
  split-no f i is p ¬pi = begin
    f i ∙ (fold f (is ∥ p) ∙ fold f (is ∥ ∁′ p))
        ≈⟨ ∙-cong refl (∙-comm _ _) ⟩
    f i ∙ (fold f (is ∥ ∁′ p) ∙ fold f (is ∥ p))
        ≈⟨ sym (assoc _ _ _) ⟩
    fold f (i ∷ (is ∥ ∁′ p)) ∙ fold f (is ∥ p)
         ≡⟨ P.sym $ P.cong₂ _∙_ (P.cong (fold f) (head-∁-no i is p ¬pi))
                                 (P.cong (fold f) (head-no i is p ¬pi)) ⟩
    fold f ((i ∷ is) ∥ ∁′ p) ∙ fold f ((i ∷ is) ∥ p)
         ≈⟨ ∙-comm _ _ ⟩
    fold f ((i ∷ is) ∥ p) ∙ fold f ((i ∷ is) ∥ ∁′ p) ∎

  -- A big operator's index list can be split using a decidable predicate
  -- ⨁[ i ← is ] f i ≈ (⨁[ i ← is ∥ p ] f i) ⊕ (⨁[ i ← is ∥ ∁′ p ] f i)

  split-P : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → (f : I → Carrier) (is : List I)
    (p : Decidable P) → fold f is ≈ fold f (is ∥ p) ∙ fold f (is ∥ ∁′ p)
  split-P f [] p = sym $ proj₁ ident _
  split-P {ℓ = ℓ} {P = P} f (i ∷ is) p =
    begin
      f i ∙ fold f is
        ≈⟨ ∙-cong refl (split-P f is p) ⟩
      f i ∙ (fold f (is ∥ p) ∙ fold f (is ∥ ∁′ p))
        ≈⌊ i ∈ p ⌋⟨ split-yes f i is p ⟩⟨ split-no f i is p ⟩
      fold f ((i ∷ is) ∥ p) ∙ fold f ((i ∷ is) ∥ ∁′ p)
    ∎
