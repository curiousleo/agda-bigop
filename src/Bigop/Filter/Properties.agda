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

head-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
           P x → (x ∷ xs) ∥ p ≡ x ∷ (xs ∥ p)
head-yes x _ p px with p x
head-yes x _ p px | yes _  = refl
head-yes x _ p px | no ¬px = ⊥-elim (¬px px)

head-∁-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
             P x → (x ∷ xs) ∥ ∁′ p ≡ xs ∥ ∁′ p
head-∁-yes x _ p px with p x
head-∁-yes x _ p px | yes _  = refl
head-∁-yes x _ p px | no ¬px = ⊥-elim (¬px px)

head-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
          ¬ P x → (x ∷ xs) ∥ p ≡ xs ∥ p
head-no x xs p ¬px with p x
head-no x xs p ¬px | yes px = ⊥-elim (¬px px)
head-no x xs p ¬px | no  _  = refl

head-∁-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
            ¬ P x → (x ∷ xs) ∥ ∁′ p ≡ x ∷ (xs ∥ ∁′ p)
head-∁-no x xs p px with p x
head-∁-no x xs p px | yes ¬px = ⊥-elim (px ¬px)
head-∁-no x xs p px | no  _   = refl

last-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs x (p : Decidable P) →
          ¬ P x → (xs ∷ʳ x) ∥ p ≡ xs ∥ p
last-no     xs       x p ¬px with p x
last-no     xs       x p ¬px | yes px = ⊥-elim (¬px px)
last-no {P} []       x p ¬px | no ¬p = head-no {P} x [] p ¬p
last-no     (y ∷ ys) x p ¬px | no ¬p with p y
last-no     (y ∷ ys) x p ¬px | no ¬p | yes _ =
                               cong (_∷_ y) $ last-no ys x p ¬p
last-no     (y ∷ ys) x p ¬px | no ¬p | no  _ = last-no ys x p ¬p

last-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs x (p : Decidable P) →
           P x → (xs ∷ʳ x) ∥ p ≡ (xs ∥ p) ∷ʳ x
last-yes xs x p t with p x
last-yes [] x p tt | yes q =               head-yes x [] p q
last-yes (y ∷ ys) x p tt | yes q with p y
last-yes (y ∷ ys) x p tt | yes q | yes _ =
                            cong (_∷_ y) $ last-yes ys x p q
last-yes (y ∷ ys) x p tt | yes q | no  _ = last-yes ys x p q
last-yes xs x p px | no ¬px = ⊥-elim (¬px px)


∥-filters : ∀ {a p} {A : Set a} {P : Pred A p} (xs : List A) (dec : Decidable P) →
            xs ∥ dec ≡ filter (⌊_⌋ ∘ dec) xs
∥-filters [] dec = refl
∥-filters (x ∷ xs) dec with dec x
∥-filters (x ∷ xs) dec | yes p = cong (_∷_ x) (∥-filters xs dec)
∥-filters (x ∷ xs) dec | no ¬p = ∥-filters xs dec

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
