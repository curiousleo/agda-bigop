module Bigop.Ordinals.Properties where

open import Bigop.Ordinals
open import Bigop.Filter

open import Data.List.Base
open import Function
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as N hiding (_⊔_; _<_)
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
           P x → (x ∷ xs) ∥ p ≡ x ∷ (xs ∥ p)
head-yes x _ p px with p x
head-yes x _ p px | yes _  = refl
head-yes x _ p px | no ¬px = ⊥-elim (¬px px)

head-∁-yes : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
             P x → (x ∷ xs) ∥ ∁-dec p ≡ xs ∥ ∁-dec p
head-∁-yes x _ p px with p x
head-∁-yes x _ p px | yes _  = refl
head-∁-yes x _ p px | no ¬px = ⊥-elim (¬px px)

head-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
          ¬ P x → (x ∷ xs) ∥ p ≡ xs ∥ p
head-no x xs p ¬px with p x
head-no x xs p ¬px | yes px = ⊥-elim (¬px px)
head-no x xs p ¬px | no  _  = refl

head-∁-no : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} x xs (p : Decidable P) →
            ¬ P x → (x ∷ xs) ∥ ∁-dec p ≡ x ∷ (xs ∥ ∁-dec p)
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

open import Data.Product

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

{-
postulatE
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
  (x ∷ xs) ∥ dec  ≡⟨ head-no x xs dec px ⟩
       xs  ∥ dec  ≡⟨ all-∁-lemma dec ¬all ⟩
  [] ∎

unique-lemma : ∀ {a p} → {A : Set a} {P : A → Set p} {xs : List A}
               (dec : Decidable P) → (u : Unique P xs) →
               xs ∥ dec ≡ [ extract-unique u ]
unique-lemma dec (here {x} {xs} px ¬all) = begin
  (x ∷ xs) ∥ dec  ≡⟨ head-yes x xs dec px ⟩
   x ∷ (xs ∥ dec) ≡⟨ cong (_∷_ x) (all-∁-lemma dec ¬all) ⟩
  [ x ] ∎
unique-lemma dec (there {x} {xs} ¬px u) = begin
  (x ∷ xs) ∥ dec  ≡⟨ head-no x xs dec ¬px ⟩
       xs  ∥ dec  ≡⟨ unique-lemma dec u ⟩
  [ extract-unique u ] ∎

open import Data.Fin using (Fin; fromℕ≤) renaming (zero to zeroF; suc to sucF)

{-
postulatE
  ordinals-unique : ∀ {m n k} → m ≤ k → k ≤ n →
                    Unique (_≡_ k) (m … n)
  ordinals-uniqueF : ∀ {m n k} → m ≤ k → (k<m+n : k < (m + n)) →
                     Unique (_≡_ (fromℕ≤ k<m+n)) (fromLenF m n)
  ordinals-eq : ∀ {m n k} → (m≤k : m ≤ k) → (k<m+n : k < (m + n)) →
                extract-unique (ordinals-uniqueF m≤k k<m+n) ≡ fromℕ≤ k<m+n
-}
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
  ordinals-filterF : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k N.< (m + n)) →
                     fromLenF m n ∥ (_≟F_ k) ≡ [ k ]

{-
ordinals-filterF : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k N.< (m + n)) →
                   fromLenF m n ∥ (_≟F_ k) ≡ [ k ]
ordinals-filterF {m} {n} {k} m≤k k<m+n = begin
  fromLenF m n ∥ (_≟F_ k)
    ≡⌊ m ~ toℕ k by compare ⌋⟨ filter< ⟩⟨ filter≈ ⟩⟨ filter> ⟩
  [ k ] ∎
  where
    open import Bigop.Filter.PredicateReasoning

    open import Relation.Binary
    open import Data.Nat.Properties using (strictTotalOrder)
    open StrictTotalOrder strictTotalOrder

    filter< : m < toℕ k → ¬ m ≈ toℕ k → ¬ toℕ k < m → fromLenF m n ∥ _≟F_ k ≡ [ k ]
    filter< m<k ¬m≈k ¬m>k = {!!}

    filter≈ : ¬ m < toℕ k → m ≈ toℕ k → ¬ toℕ k < m → fromLenF m n ∥ _≟F_ k ≡ [ k ]
    filter≈ ¬m<k m≈k ¬m>k = {!m≈k!}

    filter> : ¬ m < toℕ k → ¬ m ≈ toℕ k → toℕ k < m → fromLenF m n ∥ _≟F_ k ≡ [ k ]
    filter> ¬m<k ¬m≈k m>k = {!!}
-}

{-
-- THIS IS IT

ordinals-filterF′ : ∀ {m n k} → m ≤ k → (k<m+n : k N.< (m + n)) →
                    fromLenF m n ∥ (_≟F_ (fromℕ≤ k<m+n)) ≡ [ fromℕ≤ k<m+n ]
ordinals-filterF′ {m} {n} {k} m≤k k<m+n = begin
  fromLenF m n ∥ (_≟F_ k′)
    ≡⌊ m ~ k by compare ⌋⟨ filter< ⟩⟨ filter≈ ⟩⟨ filter> ⟩
  [ k′ ] ∎
  where
    open import Bigop.Filter.PredicateReasoning

    open import Relation.Binary
    open import Data.Nat.Properties using (strictTotalOrder)
    open StrictTotalOrder strictTotalOrder

    k′ = fromℕ≤ k<m+n

    filter< : m < k → ¬ m ≈ k → ¬ k < m → fromLenF m n ∥ _≟F_ k′ ≡ [ k′ ]
    filter< m<k ¬m≈k ¬m>k = {!!} -- recurse

    filter≈ : ¬ m < k → m ≈ k → ¬ k < m → fromLenF m n ∥ _≟F_ k′ ≡ [ k′ ]
    filter≈ ¬m<k m≈k ¬m>k = {!m≈k!} -- change tactic

    filter> : ¬ m < k → ¬ m ≈ k → k < m → fromLenF m n ∥ _≟F_ k′ ≡ [ k′ ]
    filter> ¬m<k ¬m≈k m>k = {!!} -- absurd
-}
