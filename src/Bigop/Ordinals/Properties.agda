module Bigop.Ordinals.Properties where

open import Bigop.Ordinals
open import Bigop.Filter

open import Data.List.Base
open import Function
open import Data.Nat.Base hiding (_⊔_)
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

open import Level using (_⊔_)
open import Data.Bool.Base
open import Data.List.All
open import Data.Product

data Unique {a p} {A : Set a}
            (P : A → Set p) : List A → Set (p ⊔ a) where
  here  : ∀ {x xs} ( px :   P x) → (¬all : All (∁ P) xs) → Unique P (x ∷ xs)
  there : ∀ {x xs} (¬px : ¬ P x) → (u : Unique P xs)     → Unique P (x ∷ xs)

private
 extract-unique′ : ∀ {a p} → {A : Set a} {P : A → Set p} {xs : List A} →
                   Unique P xs → Σ A P
 extract-unique′ (here {x} px ¬all) = x , px
 extract-unique′ (there ¬px u)      = extract-unique′ u

extract-unique : ∀ {a p} → {A : Set a} {P : A → Set p} {xs : List A} →
                 Unique P xs → A
extract-unique u = proj₁ (extract-unique′ u)

all-∁-lemma : ∀ {a p} → {A : Set a} {P : A → Set p} {xs : List A}
              (dec : Decidable P) → All (∁ P) xs → xs ∥ dec ≡ []
all-∁-lemma dec []                     = refl
all-∁-lemma dec (_∷_ {x} {xs} px ¬all) = begin
  (x ∷ xs) ∥ dec  ≡⟨ head-no x xs dec (fromWitnessFalse px) ⟩
       xs  ∥ dec  ≡⟨ all-∁-lemma dec ¬all ⟩
  [] ∎

unique-lemma : ∀ {a p} → {A : Set a} {P : A → Set p} {xs : List A}
               (dec : Decidable P) → (u : Unique P xs) →
               xs ∥ dec ≡ [ extract-unique u ]
unique-lemma dec (here {x} {xs} px ¬all) = begin
  (x ∷ xs) ∥ dec  ≡⟨ head-yes x xs dec (fromWitness px) ⟩
   x ∷ (xs ∥ dec) ≡⟨ cong (_∷_ x) (all-∁-lemma dec ¬all) ⟩
  [ x ] ∎
unique-lemma dec (there {x} {xs} ¬px u) = begin
  (x ∷ xs) ∥ dec  ≡⟨ head-no x xs dec (fromWitnessFalse ¬px) ⟩
       xs  ∥ dec  ≡⟨ unique-lemma dec u ⟩
  [ extract-unique u ] ∎

open import Data.Fin using (Fin; fromℕ≤) renaming (zero to zeroF; suc to sucF)

postulate
  ordinals-unique : ∀ {m n k} → m ≤ k → k ≤ n →
                    Unique (_≡_ k) (m … n)
  ordinals-uniqueF : ∀ {m n k} → m ≤ k → (k<m+n : k < (m + n)) →
                     Unique (_≡_ (fromℕ≤ k<m+n)) (fromLenF m n)
  ordinals-eq : ∀ {m n k} → (m≤k : m ≤ k) → (k<m+n : k < (m + n)) →
                extract-unique (ordinals-uniqueF m≤k k<m+n) ≡ fromℕ≤ k<m+n

{-
open import Relation.Binary

open import Data.Nat.Properties using (strictTotalOrder)
open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)
  using (compare)

ordinals-uniqueF : ∀ {m n k} → m ≤ k → (k<m+n : k < (m + n)) →
                   Unique (_≡_ (fromℕ≤ k<m+n)) (fromLenF m n)
ordinals-uniqueF {zero} {k = zero} z≤n (s≤s k≤m+n) = here {!!} {!ordinals-lt!}
ordinals-uniqueF {k = suc k} z≤n k≤m+n = {!!}
ordinals-uniqueF (s≤s m≤k) k≤m+n = {!!}
-}

open import Bigop.Filter
open import Data.Fin using (toℕ)

postulate
  ordinals-filterF : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k < (m + n)) →
                     fromLenF m n ∥ (_≟F_ k) ≡ [ k ]
