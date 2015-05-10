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

suc-lemma : ∀ m n → map suc (upFromℕ m n) ≡ upFromℕ (suc m) n
suc-lemma m zero    = refl
suc-lemma m (suc n) = cong (_∷_ (suc m)) (suc-lemma (suc m) n)

suc-head-lemma : ∀ m n → m ∷ (upFromℕ (suc m) n) ≡ upFromℕ m (suc n)
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

suc-last-lemma : ∀ m n → upFromℕ m (suc n) ≡ (upFromℕ m n) ∷ʳ (m + n)
suc-last-lemma m zero = cong (_∷ʳ_ []) $ +-comm zero m
suc-last-lemma m (suc n) = begin
  m ∷ upFromℕ (suc m) (suc n)
    ≡⟨ cong (_∷_ m) $ suc-last-lemma (suc m) n ⟩
  m ∷ (upFromℕ (suc m) n) ∷ʳ suc m + n
    ≡⟨ cong (_∷ʳ_ $ upFromℕ m (suc n)) $ sym $ +-suc m n ⟩
  upFromℕ m (suc n) ∷ʳ m + suc n ∎

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
  uniqueℕ : ∀ m n k → m ≤ k → k ≤ n → upFromℕ m n ∥ _≟_ k ≡ [ k ]
  uniqueF : ∀ m n k → m ≤ toℕ k → toℕ k ≤ (m + n) → upFromF m n ∥ _≟F_ k ≡ [ k ]
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
                     Unique (_≡_ (fromℕ≤ k<m+n)) (upFromF m n)
  ordinals-eq : ∀ {m n k} → (m≤k : m ≤ k) → (k<m+n : k < (m + n)) →
                extract-unique (ordinals-uniqueF m≤k k<m+n) ≡ fromℕ≤ k<m+n
-}
{-
open import Relation.Binary

open import Data.Nat.Properties using (strictTotalOrder)
open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)
  using (compare)

ordinals-uniqueF : ∀ {m n k} → m ≤ k → (k<m+n : k < (m + n)) →
                   Unique (_≡_ (fromℕ≤ k<m+n)) (upFromF m n)
ordinals-uniqueF {zero} {k = zero} z≤n (s≤s k≤m+n) = here {!!} {!ordinals-lt!}
ordinals-uniqueF {k = suc k} z≤n k≤m+n = {!!}
ordinals-uniqueF (s≤s m≤k) k≤m+n = {!!}
-}

open import Bigop.Filter
open import Data.Fin using (toℕ; inject+; inject≤; inject₁; fromℕ)


import Relation.Binary

≟N : Relation.Binary.Decidable {A = ℕ} _≡_
≟N zero    zero    = yes refl
≟N zero    (suc n) = no (λ ())
≟N (suc m) zero    = no (λ ())
≟N (suc m) (suc n) with ≟N m n
≟N (suc m) (suc .m) | yes refl = yes refl
≟N (suc m) (suc n)  | no ¬p    = no (suc-lem ¬p)
  where
    suc-inj : {m n : ℕ} → ℕ.suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

    suc-lem : {m n : ℕ} → ¬ m ≡ n → ¬ ((suc m) ≡ (suc n))
    suc-lem ¬m≡n sucm≡sucn rewrite suc-inj sucm≡sucn = ¬m≡n refl

ordinals-suc : ∀ m n k → k N.< m → upFromℕ m n ∥ (≟N k) ≡ []
ordinals-suc m       zero    k k<m = refl
ordinals-suc zero    (suc n) k ()
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
                   upFromℕ m n ∥ (≟N k) ≡ [ k ]
ordinals-filterℕ zero zero k z≤n ()
ordinals-filterℕ zero (suc n) zero z≤n (s≤s z≤n) = cong (_∷_ zero) (ordinals-suc 1 n 0 (s≤s z≤n))
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

open import Data.Nat.Properties using (m≤m+n)

ordinals-suc′ : ∀ m n k → toℕ k N.< m → upFromF′ m n ∥ (≟ k) ≡ []
ordinals-suc′ m zero k k<m = refl
ordinals-suc′ zero (suc n) k ()
ordinals-suc′ (suc m) (suc n) k k<m rewrite +-suc m n with ≟ k (fromℕ≤ {suc m} (s≤s (s≤s (m≤m+n m n))))
ordinals-suc′ (suc m) (suc n) .(suc (fromℕ≤ (s≤s (m≤m+n m n)))) (s≤s k<m) | yes refl = ⊥-elim (¬lt m n k<m)
  where
    ¬lt : ∀ m n → suc (toℕ (fromℕ≤ (s≤s (m≤m+n m n)))) ≤ m → ⊥
    ¬lt zero n ()
    ¬lt (suc m) n (s≤s 1+m≤n) = ¬lt m n 1+m≤n

ordinals-suc′ (suc m) (suc n) k (s≤s k<m) | no ¬p = ordinals-suc′ (suc (suc m)) n k (s≤s (lt k<m))
  where
    lt : ∀ {m n} → m ≤ n → m ≤ suc n
    lt {zero} m≤n = z≤n
    lt {suc m} {zero} ()
    lt {suc m} {suc n} (s≤s m≤n) = s≤s (lt m≤n)

open import Data.Fin.Properties using (toℕ-fromℕ≤)


ordinals-filterF′ : ∀ m n k → m ≤ toℕ k → (k<m+n : toℕ k N.< (m + n)) →
                    upFromF′ m n ∥ (≟ k) ≡ [ k ]
ordinals-filterF′ zero zero k m≤k ()
ordinals-filterF′ (suc m) zero zero () k<m+n
ordinals-filterF′ (suc m) zero (suc k) (s≤s m≤k) (s≤s k<m+n) rewrite +-comm m zero = ⊥-elim (contr m k k<m+n m≤k)
  where
    contr : ∀ m {i} (k : Fin i) → suc (toℕ k) ≤ m → m ≤ toℕ k → ⊥
    contr zero k () m≤k
    contr (suc m) {zero} () 1+k≤m m≤k
    contr (suc m) {suc i} zero 1+k≤m ()
    contr (suc m) {suc i} (suc k) (s≤s 1+k≤m) (s≤s m≤k) = contr m k 1+k≤m m≤k

ordinals-filterF′ zero (suc n) zero z≤n (s≤s z≤n) = cong (_∷_ zero) (ordinals-suc′ 1 n zero (s≤s z≤n))
ordinals-filterF′ zero (suc n) (suc k) z≤n (s≤s k<m+n) = ordinals-filterF′ 1 n (suc k) (s≤s z≤n) (s≤s k<m+n)
ordinals-filterF′ (suc m) (suc n) zero () k<m+n
ordinals-filterF′ (suc m) (suc n) (suc k) m≤k k<m+n rewrite +-suc m n with ≟ k (fromℕ≤ {m} (s≤s (m≤m+n m n)))
ordinals-filterF′ (suc m) (suc n) (suc .(fromℕ≤ (s≤s (m≤m+n m n)))) (s≤s m≤k) (s≤s (s≤s k<m+n)) | yes refl = cong (_∷_ (suc (fromℕ≤ (s≤s (m≤m+n m n))))) (ordinals-suc′ (suc (suc m)) n (suc (fromℕ≤ (s≤s (m≤m+n m n)))) (s≤s (s≤s (lt m n))))
  where
    lt : ∀ m n → toℕ (fromℕ≤ {m} (s≤s (m≤m+n m n))) ≤ m
    lt zero    n = z≤n
    lt (suc m) n = s≤s (lt m n)

ordinals-filterF′ (suc m) (suc n) (suc k) (s≤s m≤k) (s≤s (s≤s k<m+n)) | no ¬p = ordinals-filterF′ (suc (suc m)) n (suc k) (s≤s (lt m k m≤k (s≤s (m≤m+n m n)) ¬p)) (s≤s (s≤s k<m+n))
  where
    lt : ∀ m k → m ≤ toℕ k → (le : m N.< suc m + n) → ¬ k ≡ fromℕ≤ {m} le →
         suc m ≤ toℕ k
    lt zero    zero    z≤n       (s≤s z≤n)         ¬k≡m = ⊥-elim (¬k≡m refl)
    lt zero    (suc k) z≤n       (s≤s z≤n)         ¬k≡m = s≤s z≤n
    lt (suc m) zero    ()        m≤m+n             ¬k≡m
    lt (suc m) (suc k) (s≤s m≤k) (s≤s (s≤s m≤m+n)) ¬k≡m =
      s≤s (lt m k m≤k (s≤s m≤m+n) (λ z → ¬k≡m (cong suc z)))

ordinals-filterF : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k N.< (m + n)) →
                     upFromF′ m n ∥ (≟ k) ≡ [ k ]
ordinals-filterF {m} {n} {k} = ordinals-filterF′ m n k
