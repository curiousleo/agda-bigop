------------------------------------------------------------------------
-- Big operator library
--
-- Filter properties
------------------------------------------------------------------------

module Bigop.Filter.Properties where

open import Bigop.DecidableEquality
open import Bigop.Filter

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base
open import Data.Product hiding (map)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning

-- _∥_ right-distributes over _++_

∥-distrib : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs ys (p : Decidable P) →
            (xs ++ ys) ∥ p ≡ (xs ∥ p) ++ (ys ∥ p)
∥-distrib [] ys p = refl
∥-distrib (x ∷ xs) ys p with p x
... | yes px = cong (_∷_ x) (∥-distrib xs ys p)
... | no ¬px = ∥-distrib xs ys p

------------------------------------------------------------------------
-- Single-step lemmas

∥-step-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x (p : Decidable P) →
             P x → [ x ] ∥ p ≡ [ x ]
∥-step-yes x p px with p x
... | yes  _ = refl
... | no ¬px = ⊥-elim (¬px px)

∥-step-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x (p : Decidable P) →
            ¬ P x → [ x ] ∥ p ≡ []
∥-step-no x p ¬px with p x
... | yes px = ⊥-elim (¬px px)
... | no  _  = refl

head-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
           P x → (x ∷ xs) ∥ p ≡ x ∷ (xs ∥ p)
head-yes x xs p px = begin
  ([ x ] ++ xs) ∥ p        ≡⟨ ∥-distrib [ x ] xs p ⟩
  ([ x ] ∥ p) ++ (xs ∥ p)  ≡⟨ ∥-step-yes x p px ⟨ cong₂ _++_ ⟩ refl ⟩
  x ∷ (xs ∥ p)             ∎

head-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
          ¬ P x → (x ∷ xs) ∥ p ≡ xs ∥ p
head-no x xs p ¬px = begin
  ([ x ] ++ xs) ∥ p        ≡⟨ ∥-distrib [ x ] xs p ⟩
  ([ x ] ∥ p) ++ (xs ∥ p)  ≡⟨ ∥-step-no x p ¬px ⟨ cong₂ _++_ ⟩ refl ⟩
  xs ∥ p                   ∎

last-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs x (p : Decidable P) →
           P x → (xs ∷ʳ x) ∥ p ≡ (xs ∥ p) ∷ʳ x
last-yes xs x p px = begin
  (xs ++ [ x ]) ∥ p        ≡⟨ ∥-distrib xs (x ∷ []) p ⟩
  (xs ∥ p) ++ ([ x ] ∥ p)  ≡⟨ refl {x = xs ∥ p} ⟨ cong₂ _++_ ⟩ ∥-step-yes x p px ⟩
  (xs ∥ p) ++ [ x ]        ∎

last-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs x (p : Decidable P) →
          ¬ P x → (xs ∷ʳ x) ∥ p ≡ xs ∥ p
last-no xs x p ¬px = begin
  (xs ++ [ x ]) ∥ p        ≡⟨ ∥-distrib xs (x ∷ []) p ⟩
  (xs ∥ p) ++ ([ x ] ∥ p)  ≡⟨ refl {x = xs ∥ p} ⟨ cong₂ _++_ ⟩ ∥-step-no x p ¬px ⟩
  (xs ∥ p) ++ []           ≡⟨ xs++[]≡xs (xs ∥ p) ⟩
  xs ∥ p                   ∎
  where
    xs++[]≡xs : ∀ {a} {A : Set a} (xs : List A) → xs ++ [] ≡ xs
    xs++[]≡xs [] = refl
    xs++[]≡xs (x ∷ xs) = cong (_∷_ x) (xs++[]≡xs xs)

head-∁-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
             P x → (x ∷ xs) ∥ ∁′ p ≡ xs ∥ ∁′ p
head-∁-yes {P = P} x xs p px = head-no x xs (∁′ p) (λ ¬px → ¬px px)

head-∁-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
            ¬ P x → (x ∷ xs) ∥ ∁′ p ≡ x ∷ (xs ∥ ∁′ p)
head-∁-no x xs p ¬px = head-yes x xs (∁′ p) ¬px

------------------------------------------------------------------------
-- _∥_ is equivalent to the standard library function "filter"

∥-filters : ∀ {a p} {A : Set a} {P : Pred A p} (xs : List A) (dec : Decidable P) →
            xs ∥ dec ≡ filter (⌊_⌋ ∘ dec) xs
∥-filters [] dec = refl
∥-filters (x ∷ xs) dec with dec x
∥-filters (x ∷ xs) dec | yes p = cong (_∷_ x) (∥-filters xs dec)
∥-filters (x ∷ xs) dec | no ¬p = ∥-filters xs dec

------------------------------------------------------------------------
-- _∥_ behaves as expected when decidable predicates are intersected

combine-filters : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
                  (xs : List A) (dec-p : Decidable P) (dec-q : Decidable Q)
                  (dec-p∩q : Decidable (P ∩ Q)) →
                  (xs ∥ dec-p) ∥ dec-q ≡ xs ∥ dec-p∩q
combine-filters [] p q p∩q = refl
combine-filters (x ∷ xs) p q p∩q with p x | q x | p∩q x
combine-filters (x ∷ xs) p q p∩q | yes px | yes qx | yes p∩qx = begin
  (x ∷ (xs ∥ p)) ∥ q  ≡⟨ head-yes x (xs ∥ p) q qx ⟩
  x ∷ ((xs ∥ p) ∥ q)  ≡⟨ cong (_∷_ x) (combine-filters xs p q p∩q) ⟩
  x ∷ (xs ∥ p∩q)      ∎
combine-filters (x ∷ xs) p q p∩q | yes px | yes qx | no ¬p∩qx = ⊥-elim (¬p∩qx (px , qx))
combine-filters (x ∷ xs) p q p∩q | yes px | no ¬qx | yes p∩qx = ⊥-elim (¬qx (proj₂ p∩qx))
combine-filters (x ∷ xs) p q p∩q | yes px | no ¬qx | no ¬p∩qx = begin
  (x ∷ (xs ∥ p)) ∥ q  ≡⟨ head-no x (xs ∥ p) q ¬qx ⟩
  (xs ∥ p) ∥ q        ≡⟨ combine-filters xs p q p∩q ⟩
  xs ∥ p∩q            ∎
combine-filters (x ∷ xs) p q p∩q | no ¬px | yes qx | yes p∩qx = ⊥-elim (¬px (proj₁ p∩qx))
combine-filters (x ∷ xs) p q p∩q | no ¬px | yes qx | no ¬p∩qx = combine-filters xs p q p∩q
combine-filters (x ∷ xs) p q p∩q | no ¬px | no ¬qx | yes p∩qx = ⊥-elim (¬qx (proj₂ p∩qx))
combine-filters (x ∷ xs) p q p∩q | no ¬px | no ¬qx | no ¬p∩qx = combine-filters xs p q p∩q
