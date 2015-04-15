module Bigop.Ordinals.Properties where

open import Bigop.Ordinals
open import Bigop.Filter

open import Data.List.Base
open import Function
open import Data.Nat.Base
open import Data.Nat.Properties.Simple
-- open import Data.Nat
-- open import Data.Fin hiding (_+_; _≤_)
-- open import Data.Fin.Properties renaming (_≟_ to _≟F_)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning

suc-lemma : ∀ m n → map suc (fromLenℕ m n) ≡ fromLenℕ (suc m) n
suc-lemma m zero    = refl
suc-lemma m (suc n) = cong (_∷_ (suc m)) (suc-lemma (suc m) n)

suc-head-lemma : ∀ m n → m ∷ (fromLenℕ (suc m) n) ≡ fromLenℕ m (suc n)
suc-head-lemma m n = refl

suc-last-lemma : ∀ m n → fromLenℕ m (suc n) ≡ (fromLenℕ m n) ∷ʳ (m + n)
suc-last-lemma m zero = cong (_∷ʳ_ []) $ +-comm zero m
suc-last-lemma m (suc n) = begin
  m ∷ fromLenℕ (suc m) (suc n)
    ≡⟨ cong (_∷_ m) $ suc-last-lemma (suc m) n ⟩
  m ∷ (fromLenℕ (suc m) n) ∷ʳ suc m + n
    ≡⟨ cong (_∷ʳ_ $ fromLenℕ m (suc n)) $ sym $ +-suc m n ⟩
  fromLenℕ m (suc n) ∷ʳ m + suc n ∎

head-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
           True (p x) → (x ∷ xs) ∥ p ≡ x ∷ (xs ∥ p)
head-yes x xs p t with p x
head-yes x xs p t  | yes _ = refl
head-yes x xs p () | no  _

head-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
          False (p x) → (x ∷ xs) ∥ p ≡ xs ∥ p
head-no x xs p f with p x
head-no x xs p () | yes _
head-no x xs p tt | no  _ = refl

last-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs x (p : Decidable P) →
          False (p x) → (xs ∷ʳ x) ∥ p ≡ xs ∥ p
last-no     xs       x p f with p x
last-no     xs       x p () | yes _
last-no {P} []       x p tt | no ¬p =     head-no {P} x [] p (fromWitnessFalse ¬p)
last-no     (y ∷ ys) x p tt | no ¬p with p y
last-no     (y ∷ ys) x p tt | no ¬p | yes _ =
                               cong (_∷_ y) $ last-no ys x p (fromWitnessFalse ¬p)
last-no     (y ∷ ys) x p tt | no ¬p | no  _ = last-no ys x p (fromWitnessFalse ¬p)

last-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} xs x (p : Decidable P) →
           True (p x) → (xs ∷ʳ x) ∥ p ≡ (xs ∥ p) ∷ʳ x
last-yes xs x p t with p x
last-yes [] x p tt | yes q =               head-yes x [] p (fromWitness q)
last-yes (y ∷ ys) x p tt | yes q with p y
last-yes (y ∷ ys) x p tt | yes q | yes _ =
                            cong (_∷_ y) $ last-yes ys x p (fromWitness q)
last-yes (y ∷ ys) x p tt | yes q | no  _ = last-yes ys x p (fromWitness q)
last-yes xs x p () | no  _

{-
postulate
  uniqueℕ : ∀ m n k → m ≤ k → k ≤ n → fromLenℕ m n ∥ _≟_ k ≡ [ k ]
  uniqueF : ∀ m n k → m ≤ toℕ k → toℕ k ≤ (m + n) → fromLenF m n ∥ _≟F_ k ≡ [ k ]
-}
