module Bigop.Ordinals.Properties where

open import Bigop.Ordinals
open import Bigop.Filter

import Data.List.Base as L
open L
open import Function
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as N hiding (_⊔_; _<_)
open import Data.Nat.Properties.Simple
-- open import Data.Nat
open import Data.Fin hiding (_+_; _≤_; lift)
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

{-

open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc; +-comm)
open import Data.Fin.Properties using (toℕ-fromℕ≤)

lift-id : ∀ m {n} → toℕ (lift m {n}) ≡ m
lift-id m {n} = toℕ-fromℕ≤ (s≤s (m≤m+n m n))

import Data.Vec as V

∷ʳ-map : ∀ {a b n} → {A : Set a} {B : Set b} (f : A → B) (xs : V.Vec A n) (x : A) →
         V.map f (xs V.∷ʳ x) ≡ V.map f xs V.∷ʳ f x
∷ʳ-map f V.[] x = refl
∷ʳ-map f (y V.∷ ys) x = cong (V._∷_ (f y)) (∷ʳ-map f ys x)

head-lemma′ : ∀ from len → ι-nat-vec-rev from (suc len) ≡
                           from + len V.∷ ι-nat-vec-rev (suc from) len
head-lemma′ from zero = begin
 V.map toℕ (lift (from + zero) V.∷ V.[])
   ≡⟨ {!ι-fin-vec-rev from 1!} ⟩
 from + 0 V.∷ V.[] ∎
head-lemma′ from (suc len) = {!!}

suc-last-lemma′ : ∀ from len → ι-nat-vec-rev from (suc len) ≡
                               (ι-nat-vec-rev (suc from) len) V.∷ʳ from
suc-last-lemma′ from len rewrite +-suc from len = begin
  V.map toℕ (ι-fin-vec-rev (suc from) len V.∷ʳ lift from)
    ≡⟨ ∷ʳ-map toℕ (ι-fin-vec-rev (suc from) len) (fromℕ≤ (s≤s (m≤m+n from len))) ⟩
  V.map toℕ (ι-fin-vec-rev (suc from) len) V.∷ʳ toℕ (lift from)
    ≡⟨ cong (V._∷ʳ_ (V.map toℕ (ι-fin-vec-rev (suc from) len))) (lift-id from) ⟩
  V.map toℕ (ι-fin-vec-rev (suc from) len) V.∷ʳ from ∎

-- REDEFINE ι-nat-list-rev : swap toList and `map toℕ`

suc-last-lemma″ : ∀ from len → ι-nat-list-rev from (suc len) ≡
                               (ι-nat-list-rev (suc from) len) ∷ʳ from
suc-last-lemma″ from len rewrite +-suc from len = cong V.toList {!suc-last-lemma′!}
{-
begin
  map toℕ (V.toList (ι-fin-vec-rev (suc from) len V.∷ʳ lift from))
    ≡⟨ cong (map toℕ) (∷ʳ-to-∷ʳ (ι-fin-vec-rev (suc from) len) (fromℕ≤ (s≤s (m≤m+n from len)))) ⟩
  map toℕ (V.toList (ι-fin-vec-rev (suc from) len) ∷ʳ lift from)
    ≡⟨ {!∷ʳ-map!} ⟩
  map toℕ (V.toList (ι-fin-vec-rev (suc from) len)) ∷ʳ toℕ (lift from)
    ≡⟨ cong (_∷ʳ_ (map toℕ (V.toList (ι-fin-vec-rev (suc from) len)))) (lift-id from) ⟩
  map toℕ (V.toList (ι-fin-vec-rev (suc from) len)) ∷ʳ from ∎
  where
    ∷ʳ-to-∷ʳ : ∀ {a n} → {A : Set a} (xs : V.Vec A n) (x : A) →
               V.toList (xs V.∷ʳ x) ≡ V.toList xs L.∷ʳ x
    ∷ʳ-to-∷ʳ V.[] x = refl
    ∷ʳ-to-∷ʳ (y V.∷ ys) x = begin
      y ∷ V.toList (ys V.∷ʳ x)  ≡⟨ cong (_∷_ y) (∷ʳ-to-∷ʳ ys x) ⟩
      y ∷ V.toList ys ∷ʳ x      ∎
-}
-}

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

open import Data.Product hiding (map)

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

{-
postulatE
  uniqueℕ : ∀ m n k → m ≤ k → k ≤ n → fromLenℕ m n ∥ _≟_ k ≡ [ k ]
  uniqueF : ∀ m n k → m ≤ toℕ k → toℕ k ≤ (m + n) → fromLenF m n ∥ _≟F_ k ≡ [ k ]
-}

open import Level using (_⊔_)
open import Data.Bool.Base
open import Data.List.All hiding (head; tail; tabulate; map; lookup)
open import Data.Product hiding (map)

import Data.Vec as V
open V hiding ([_])

All-Vec : ∀ {a p n} → {A : Set a} (P : A → Set p) → Vec A n → Set (p ⊔ a)
All-Vec P xs = All P (toList xs)

data Unique {a p} {A : Set a}
            (P : A → Set p) : List A → Set (p ⊔ a) where
  here  : ∀ {x xs} ( px :   P x) → (¬all : All (∁ P) xs) → Unique P (x ∷ xs)
  there : ∀ {x xs} (¬px : ¬ P x) → (u : Unique P xs)     → Unique P (x ∷ xs)

Unique-Vec : ∀ {a p n} {A : Set a} (P : A → Set p) → Vec A n → Set (p ⊔ a)
Unique-Vec P xs = Unique P (toList xs)

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
open import Data.Fin using (toℕ; inject+; inject≤; inject₁; fromℕ)

postulate
  ordinals-filterF : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k N.< (m + n)) →
                     fromLenF m n ∥ (≟ k) ≡ [ k ]

import Relation.Binary

≟N : Relation.Binary.Decidable {A = ℕ} _≡_
≟N zero zero = yes refl
≟N zero (suc n) = no (λ ())
≟N (suc m) zero = no (λ ())
≟N (suc m) (suc n) with ≟N m n
≟N (suc m) (suc .m) | yes refl = yes refl
≟N (suc m) (suc n) | no ¬p = no (suc-lem ¬p)
  where
    suc-inj : {m n : ℕ} → ℕ.suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

    suc-lem : {m n : ℕ} → ¬ m ≡ n → ¬ ((suc m) ≡ (suc n))
    suc-lem ¬m≡n sucm≡sucn rewrite suc-inj sucm≡sucn = ¬m≡n refl

ordinals-suc : ∀ m n k → k N.< m → fromLenℕ m n ∥ (≟N k) ≡ []
ordinals-suc m zero k k<m = refl
ordinals-suc zero (suc n) k ()
ordinals-suc (suc m) (suc n) k k<m with ≟N k (suc m)
ordinals-suc (suc m) (suc n) .(suc m) (s≤s k<m) | yes refl = ⊥-elim (¬lt k<m)
  where
    ¬lt : ∀ {m} → suc m ≤ m → ⊥
    ¬lt {zero} ()
    ¬lt {suc m} (s≤s m+1≤m) = ¬lt m+1≤m

ordinals-suc (suc m) (suc n) k (s≤s k<m) | no ¬p = ordinals-suc (suc (suc m)) n k (s≤s (lt k<m))
  where
    lt : ∀ {m n} → m ≤ n → m ≤ suc n
    lt {zero} m≤n = z≤n
    lt {suc m} {zero} ()
    lt {suc m} {suc n} (s≤s m≤n) = s≤s (lt m≤n)

ordinals-filterℕ : ∀ m n k → m ≤ k → (k<m+n : k N.< (m + n)) →
                   fromLenℕ m n ∥ (≟N k) ≡ [ k ]
ordinals-filterℕ zero zero zero z≤n ()
ordinals-filterℕ zero (suc n) zero z≤n (s≤s z≤n) = cong (_∷_ zero) (ordinals-suc 1 n 0 (s≤s z≤n))
ordinals-filterℕ zero zero (suc k) z≤n ()
ordinals-filterℕ zero (suc n) (suc k) z≤n (s≤s k<m+n) = ordinals-filterℕ 1 n (suc k) (s≤s z≤n) (s≤s k<m+n)
ordinals-filterℕ (suc m) n zero () k<m+n
ordinals-filterℕ (suc m) zero (suc k) (s≤s m≤k) (s≤s k<m+n) rewrite +-comm m zero = ⊥-elim (contr k<m+n m≤k)
  where
    contr : ∀ {m k} → suc k ≤ m → m ≤ k → ⊥
    contr {zero} {k} () m≤k
    contr {suc m} {zero} (s≤s k+1≤m) ()
    contr {suc m} {suc k} (s≤s k+1≤m) (s≤s m≤k) = contr k+1≤m m≤k

ordinals-filterℕ (suc m) (suc n) (suc k) (s≤s m≤k) (s≤s k<m+n) with ≟N k m
ordinals-filterℕ (suc m) (suc n) (suc .m) (s≤s m≤k) (s≤s k<m+n) | yes refl = cong (_∷_ (suc m)) (ordinals-suc (suc (suc m)) n (suc m) (s≤s (s≤s m≤k)))
ordinals-filterℕ (suc m) (suc n) (suc k) (s≤s m≤k) (s≤s k<m+n) | no ¬p rewrite +-suc m n = ordinals-filterℕ (suc (suc m)) n (suc k) (s≤s (lt m k m≤k ¬p)) (s≤s k<m+n)
  where
    suc-lem : ∀ {m n} → ¬ suc m ≡ suc n → ¬ m ≡ n
    suc-lem ¬eq refl = ¬eq refl

    lt : ∀ m k → m ≤ k → ¬ k ≡ m → suc m ≤ k
    lt zero zero z≤n ¬k≡m = ⊥-elim (¬k≡m refl)
    lt (suc m) zero () ¬k≡m
    lt zero (suc k) z≤n ¬k≡m = s≤s z≤n
    lt (suc m) (suc k) (s≤s m≤k) ¬k≡m = s≤s (lt m k m≤k (suc-lem ¬k≡m))

{-
open import Data.Nat using () renaming (_≟_ to _≟N_)
open import Data.Maybe hiding (map; All)

headMaybe : ∀ {a} → {A : Set a} → List A → Maybe A
headMaybe []      = nothing
headMaybe (x ∷ _) = just x

fromLenℕ-head : ∀ {m n} → headMaybe (fromLenℕ m (suc n)) ≡ just m
fromLenℕ-head = refl

open import Data.Nat.Properties.Simple using (+-comm)

ordinals-filterℕ : ∀ {m n k} → m ≤ k → (k<m+n : k N.< (m + n)) →
                   fromLenℕ m n ∥ (_≟N_ k) ≡ [ k ]
ordinals-filterℕ {m} {n} {k} m≤k k<m+n with m ≟N k
ordinals-filterℕ {m} {zero} m≤k k<m+n | yes refl = ⊥-elim (¬m+1≤m+0 k<m+n)
  where
    ¬m+1≤m : ∀ {m} → ¬ suc m ≤ m
    ¬m+1≤m {zero} ()
    ¬m+1≤m {suc m} (s≤s le) = ¬m+1≤m le

    ¬m+1≤m+0 : ∀ {m} → ¬ suc m ≤ m + 0
    ¬m+1≤m+0 {zero} ()
    ¬m+1≤m+0 {suc m} (s≤s le) rewrite +-comm m 0 = ¬m+1≤m le

ordinals-filterℕ {m} {suc n} m≤k k<m+n | yes refl rewrite +-comm m (suc n) = head-yes m (fromLenℕ (suc m) {!m!}) (_≟N_ {!m!}) {!refl {x = m}!}
ordinals-filterℕ {n = n} m≤k k<m+n | no ¬p = {!!}
-}
{-
ordinals-filterF : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k N.< (m + n)) →
                   fromLenF m n ∥ (≟ k) ≡ [ k ]
ordinals-filterF {m} {n} {k} m≤k k<m+n = begin
  fromLenF m n ∥ (≟ k)
    ≡⌊ m ~ toℕ k by compare ⌋⟨ filter< ⟩⟨ filter≈ ⟩⟨ filter> ⟩
  [ k ] ∎
  where
    open import Bigop.Filter.PredicateReasoning

    open import Relation.Binary
    open import Data.Nat.Properties using (strictTotalOrder)
    open StrictTotalOrder strictTotalOrder

    filter< : m < toℕ k → ¬ m ≈ toℕ k → ¬ toℕ k < m → fromLenF m n ∥ ≟ k ≡ [ k ]
    filter< m<k ¬m≈k ¬m>k = {!!}

    filter≈ : ¬ m < toℕ k → m ≈ toℕ k → ¬ toℕ k < m → fromLenF m n ∥ ≟ k ≡ [ k ]
    filter≈ ¬m<k m≈k ¬m>k = {!m≈k!}

    filter> : ¬ m < toℕ k → ¬ m ≈ toℕ k → toℕ k < m → fromLenF m n ∥ ≟ k ≡ [ k ]
    filter> ¬m<k ¬m≈k m>k = {!!}
-}

{-

downFromF : (n : ℕ) → List (Fin n)
downFromF zero = []
downFromF (suc n) = fromℕ≤ {n} (s≤s ≤-refl) ∷ map inject₁ (downFromF n)
  where
    ≤-refl : ∀ {n} → n ≤ n
    ≤-refl {zero} = z≤n
    ≤-refl {suc n} = s≤s ≤-refl

test : downFromF 3 ≡ (sucF (sucF zeroF)) ∷ sucF zeroF ∷ zeroF ∷ []
test = refl

lemma : ∀ {m n} → n ≤ m + suc n
lemma = {!!}

fromLenF-head : ∀ {m n} → headMaybe (fromLenF m (suc n)) ≡ just (inject+ {!!} {!!})
fromLenF-head {m} {n} = {!!}

ordinals-∉ : ∀ {m n k} → k N.< m → (k<m+n : k N.< (m + n)) →
             fromLenF m n ∥ (≟ (fromℕ≤ k<m+n)) ≡ []
ordinals-∉ {m} {n} {k} k<m k<m+n with fromLenF m n
ordinals-∉ k<m k<m+n | [] = refl
ordinals-∉ {m} k<m k<m+n | x ∷ xs = {!x!}

ordinals-uniqueF : ∀ {m n k} → m ≤ k → (k<m+n : k N.< (m + n)) →
                   Unique (_≡_ (fromℕ≤ k<m+n)) (fromLenF m n)
ordinals-uniqueF {m} {n} {k} m≤k k<m+n with m ≟N k
ordinals-uniqueF m≤k k<m+n | yes refl = {!here!}
ordinals-uniqueF m≤k k<m+n | no ¬p = {!!}


ordinals-filterF′ : ∀ {m n k} → m ≤ k → (k<m+n : k N.< (m + n)) →
                    fromLenF m n ∥ (≟ (fromℕ≤ k<m+n)) ≡ [ fromℕ≤ k<m+n ]
ordinals-filterF′ {m} {n} {k} m≤k k<m+n = begin
  fromLenF m n ∥ (≟ k′)
    ≡⌊ m ~ k by compare ⌋⟨ filter< ⟩⟨ filter≈ ⟩⟨ filter> ⟩
  [ k′ ] ∎
  where
    open import Bigop.Filter.PredicateReasoning

    open import Relation.Binary
    open import Data.Nat.Properties using (strictTotalOrder)
    open StrictTotalOrder strictTotalOrder

    k′ = fromℕ≤ k<m+n

    filter< : m < k → ¬ m ≈ k → ¬ k < m → fromLenF m n ∥ ≟ k′ ≡ [ k′ ]
    filter< m<k ¬m≈k ¬m>k = {!!} -- recurse

    filter≈ : ¬ m < k → m ≈ k → ¬ k < m → fromLenF m n ∥ ≟ k′ ≡ [ k′ ]
    filter≈ ¬m<k m≈k ¬m>k = {!m≈k!} -- change tactic

    filter> : ¬ m < k → ¬ m ≈ k → k < m → fromLenF m n ∥ ≟ k′ ≡ [ k′ ]
    filter> ¬m<k ¬m≈k m>k = {!!} -- absurd
-}

{-
open import Data.Fin hiding (compare)

[]=-tabulate : ∀ {n a} {A : Set a} (f : Fin n → A) i → tabulate f [ i ]= f i
[]=-tabulate f zero    = here
[]=-tabulate f (suc i) = there ([]=-tabulate (f ∘ suc) i)

ι-lemma : ∀ from {len} n → ι-fin-vec from (suc len) [ n ]= raise from n
ι-lemma from n = []=-tabulate (raise from) n

raise-inj₂ : ∀ {k} n (i j : Fin k) → raise n i ≡ raise n j → i ≡ j
raise-inj₂ zero    i .i refl = refl
raise-inj₂ (suc n) i  j eq   = raise-inj₂ n i j (suc-inj (raise n i) (raise n j) eq)
  where
    suc-inj : ∀ {k} (i j : Fin k) → Data.Fin.suc i ≡ suc j → i ≡ j
    suc-inj i j eq with ≟ i j
    suc-inj _       _        _    | yes p = p
    suc-inj zero    zero     refl | no ¬p = ⊥-elim (¬p refl)
    suc-inj zero    (suc _)  ()   | no ¬p
    suc-inj (suc _) zero     ()   | no ¬p
    suc-inj (suc _) (suc ._) refl | no ¬p = ⊥-elim (¬p refl)

ι-lemma′ : ∀ from {len} n → raise from n V.∈ ι-fin-vec from (suc len)
ι-lemma′ from n = ∈-tabulate (raise from) n
  where
    open import Data.Vec.Properties

-- also have ∈⇒List-∈ []=↔lookup lookup∘tabulate

ι-lemma″ : ∀ from {len} i → lookup i (ι-fin-vec from (suc len)) ≡ raise from i
ι-lemma″ from i = lookup∘tabulate (raise from) i
  where
    open import Data.Vec.Properties

lookupMaybe : ∀ {a} {A : Set a} (i : ℕ) (xs : List A) → Maybe A
lookupMaybe _       []       = nothing
lookupMaybe zero    (x ∷ _ ) = just x
lookupMaybe (suc i) (_ ∷ xs) = lookupMaybe i xs

import Data.List.Any as Any
module M = Any.Membership-≡

∈→lookup : ∀ {a} {A : Set a} {x : A} {xs : List A} →
           x M.∈ xs → ∃ λ i → lookupMaybe i xs ≡ just x
∈→lookup (Any.here px) = zero , sym (cong just px)
∈→lookup (Any.there x∈xs) with ∈→lookup x∈xs
∈→lookup (Any.there x∈xs) | i , eq = suc i , eq
-}
{-
module _ where
  import Relation.Binary.Vec.Pointwise as PW

  open import Data.Vec.Properties
  open import Data.Fin.Properties

  _PW-≡_ : ∀ {a} {A : Set a} {n} (xs : Vec A n) (ys : Vec A n) → Set a
  _PW-≡_ = PW.Pointwise _≡_

  _PW-≡toℕ_ : ∀ {m n k} (xs : Vec (Fin m) k) (ys : Vec (Fin n) k) → Set
  _PW-≡toℕ_ = PW.Pointwise (λ x y → toℕ x ≡ toℕ y)

  ι-split : ∀ from {len} →
            _PW-≡toℕ_ (V.tail (ι-fin-vec′ from (suc len))) (V.map suc (ι-fin-vec′ from len))
  ι-split from {len} = PW.ext (λ i → subst₂ _≡_ (sym (left i)) (sym (right i)) refl)
    where
      left : ∀ i → toℕ (lookup i (V.tail (ι-fin-vec′ from (suc len)))) ≡ suc (from N.+ toℕ i)
      left i = {!(V.replicate fin-swap ⊛ tabulate {len} (raise from ∘ suc))!}
      right : ∀ i → toℕ (lookup i (V.map suc (ι-fin-vec′ from len))) ≡ suc (from N.+ toℕ i)
      right i = {!!}


  ι-next : ∀ from {len} f →
           _PW-≡_ {A = Fin {!(V.map (f ∘ suc) (ι-fin-vec from (suc len)))!}} (V.map (f ∘ suc) (ι-fin-vec from (suc len)))
                             (V.map f (ι-fin-vec (suc from) (suc len)))
  ι-next from {len} f = PW.ext next
    where
      next : ∀ i → lookup i (V.map (f ∘ suc) (ι-fin-vec from (suc len))) ≡
                   lookup i (V.map f (ι-fin-vec (suc from) (suc len)))
      next i = {!lookup∘tabulate (f ∘ suc ∘ raise from) i!}

      left : ∀ i → lookup i (V.map (f ∘ suc) (ι-fin-vec from (suc len))) ≡
                   f (suc (raise from i))
      left i {- rewrite ι-lemma″ from {len} i -} = {!!} -- lookup∘tabulate (f ∘ suc ∘ raise from) i


  next : ∀ from {len} →
         ι-fin-vec (suc from) len ≡ V.map suc (ι-fin-vec from len)
  next from = tabulate-∘ suc (raise from)

  fin-cong : ∀ {m n} → m ≡ n → Fin m ≡ Fin n
  fin-cong refl = cong Fin refl


  open import Relation.Binary.Core using (Trichotomous)

  cmp : ∀ n → Trichotomous _≡_ (λ z z₁ → toℕ z N.< toℕ z₁)
  cmp n = compare
    where
      open import Relation.Binary using (module StrictTotalOrder; module IsStrictTotalOrder)
      open import Data.Fin.Properties using (strictTotalOrder)
      open StrictTotalOrder (strictTotalOrder n) using (isStrictTotalOrder)
      open IsStrictTotalOrder isStrictTotalOrder using (compare)

  open import Data.Nat.Properties.Simple

  ι-none : ∀ from len k → toℕ k N.< from → ι-fin-list from len ∥ (≟ k) ≡ []
  ι-none zero len k ()
  ι-none (suc from) zero k k<from = refl
  ι-none (suc from) (suc len) zero (s≤s z≤n) = {!!}
  ι-none (suc from) (suc len) (suc k) (s≤s k<from) with k ≟F raise from zero
  ... | yes eq rewrite eq = {!!}
  ... | no ¬eq = {!L.map suc (ι-fin-list from len)!}

  ι-single : ∀ from len k →
             from N.≤ toℕ k → toℕ k N.< (from N.+ len) →
             ι-fin-list from len ∥ (≟ k) ≡ [ k ]
  ι-single zero zero () from≤k k<from+len
  ι-single (suc from) zero zero () (s≤s k<from+len)
  ι-single (suc from) zero (suc k) (s≤s from≤k) (s≤s k<from+len) = ⊥-elim (lemma k from k<from+len from≤k)
    where
      lemma : ∀ {i} (m : Fin i) n → suc (toℕ m) N.≤ n N.+ zero → ¬ n N.≤ toℕ m
      lemma m zero () z≤n
      lemma zero (suc n) (s≤s 1+m≤n) ()
      lemma (suc m) (suc n) (s≤s 1+m≤n) (s≤s n≤m) = lemma m n 1+m≤n n≤m
  ι-single from (suc len) k from≤k k<from+len with k ≟F raise from zero
  ... | yes eq rewrite eq = cong {!_∷_ (raise from zero)!} (ι-none (suc from) len (+-suc-fin from len k) {!k<1+from!})
    where
      +-suc-fin : ∀ m n → Fin (m N.+ suc n) → Fin (suc m N.+ n)
      +-suc-fin k l = {!!}

      k<1+from : toℕ k N.< suc from
      k<1+from = {!!}
  ... | no ¬eq = {!!}

  ι-single′ : ∀ len k → toℕ k N.< len → ι-fin-list 0 len ∥ (≟ k) ≡ [ k ]
  ι-single′ zero k ()
  ι-single′ (suc len) zero (s≤s z≤n) = cong (_∷_ zero) {!!}
  ι-single′ (suc len) (suc k) (s≤s k<len) = {!c!}

  raise-suc : ∀ {k} m {n : Fin k} → toℕ (raise m (suc n)) ≡ toℕ (suc (raise m n))
  raise-suc m {n} = begin
    toℕ (raise m (suc n))  ≡⟨ toℕ-raise m (suc n) ⟩
    m N.+ suc (toℕ n)      ≡⟨ +-suc m (toℕ n) ⟩
    suc (m N.+ toℕ n)      ≡⟨ cong suc (sym (toℕ-raise m n)) ⟩
    toℕ (suc (raise m n))  ∎

  ι-suc : ∀ from len → L.map suc (ι-fin-list from len) ≡ ι-fin-list (suc from) len
  ι-suc from zero = refl
  ι-suc from (suc len) = cong (_∷_ (suc (raise from zero))) {!ι-suc (suc from) len!}

ι-≥from : ∀ from {len} → All (N._≤_ from) (ι-nat-list from len)
ι-≥from from {zero} = []
ι-≥from from {suc len} = {!!} ∷ {!ι-≥from!}


ι-list-lemma : ∀ from {len} i →
               lookupMaybe (toℕ i) (toList (ι-fin-vec from (suc len)))
               ≡ just (raise from i)
ι-list-lemma from i = {!!}


ι-∃! : ∀ from {len} n →
       ∃! _≡_ λ i → lookup i (ι-fin-vec from (suc len)) ≡ raise from n
ι-∃! f {len} n = n , lookup∘tabulate (raise f) n , unique
  where
    open import Data.Vec.Properties using (lookup∘tabulate)
    unique : ∀ {i} → lookup i (ι-fin-vec f (suc len)) ≡ raise f n → n ≡ i
    unique {i} eq rewrite lookup∘tabulate (raise f) i = raise-inj₂ f n i (sym eq)

lookup→List : ∀ {a n} {A : Set a} {x : A} (i : Fin n) xs →
              lookup i xs ≡ x → lookupMaybe (toℕ i) (toList xs) ≡ just x
lookup→List zero    (x ∷ _ ) refl = refl
lookup→List (suc i) (_ ∷ xs) eq   = lookup→List i xs eq

ι-unique : ∀ from len n →
           ι-fin-list from (suc len) ∥ (≟ (raise from n)) ≡
           [ raise from n ]
ι-unique zero len zero = cong (_∷_ zero) {!!}
ι-unique (suc from) zero zero = head-yes (suc (raise from zero)) {!!} {!!} {!!}
ι-unique (suc from) (suc len) zero = head-yes (suc (raise from zero)) {!!} {!!} {!!}
ι-unique from len (suc n) = {!!}


ι-unique : ∀ from {len} i → from N.≤ toℕ i →
           Unique-Vec (_≡_ i) (ι-fin-vec from (suc len))
ι-unique from i from≤i = {!!}


ι-filter : ∀ from {len} n → ι-fin-list from (suc len) ∥ (≟ n) ≡ Data.List.Base.[ n ]
ι-filter from n = {!!}
-}
