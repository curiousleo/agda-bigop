module Bigop.Ordinals where

open import Data.List hiding (_∷ʳ_)
open import Data.Fin hiding (_≤_; _+_; lift)
open import Data.Nat
open import Function using (_∘_)

range : ∀ {from to} → from ≤ to → List (Fin to)
range (z≤n {zero})          = []
range (z≤n {suc to})        = zero ∷ map suc (range (z≤n {to}))
range (s≤s {from} {to} f≤t) = map suc (range f≤t)

fromLenF : (from len : ℕ) → List (Fin (from + len))
fromLenF from len = range {from} {from + len} (m≤m+n from len)
  where open import Data.Nat.Properties using (m≤m+n)

fromLenℕ : ℕ → ℕ → List ℕ
fromLenℕ from zero = []
fromLenℕ from (suc len) = from ∷ fromLenℕ (suc from) len

open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc)

fromLenF′ : (from len : ℕ) → List (Fin (from + len))
fromLenF′ from zero = []
fromLenF′ from (suc len) rewrite +-suc from len = fromℕ≤ {from} (s≤s (m≤m+n from len)) ∷ fromLenF′ (suc from) len

downFromLenℕ : ℕ → ℕ → List ℕ
downFromLenℕ zero       zero      = []
downFromLenℕ (suc _)    zero      = []
downFromLenℕ zero       (suc len) = [ zero ]
downFromLenℕ (suc from) (suc len) = suc from ∷ downFromLenℕ from len

_…+_ = fromLenℕ
_…-_ = downFromLenℕ

infix 6 _…_

_…_ : ℕ → ℕ → List ℕ
m … n = m …+ (suc n ∸ m)

_…↓_ : ℕ → ℕ → List ℕ
m …↓ n = m …- (suc m ∸ n)

import Data.Vec as V
open V
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc)

ι-fin-vec : (from : ℕ) → (len : ℕ) → Vec (Fin (from + len)) len
ι-fin-vec from len = tabulate {len} (raise from)

lift : ∀ m {n} → Fin (suc m + n)
lift m {n} = fromℕ≤ {m} (s≤s (m≤m+n m n))

ι-fin-vec-rev : (from : ℕ) → (len : ℕ) → Vec (Fin (from + len)) len
ι-fin-vec-rev from zero = []
ι-fin-vec-rev from (suc len) rewrite +-suc from len = ι-fin-vec-rev (suc from) len ∷ʳ lift from

ι-nat-vec-rev : ∀ from len → Vec ℕ len
ι-nat-vec-rev from len = V.map toℕ (ι-fin-vec-rev from len)

ι-fin-list-rev : (from : ℕ) → (len : ℕ) → List (Fin (from + len))
ι-fin-list-rev from len = toList (ι-fin-vec-rev from len)

ι-nat-list-rev : (from : ℕ) → (len : ℕ) → List ℕ
ι-nat-list-rev from len = toList (ι-nat-vec-rev from len)

module _ where
  open import Relation.Binary.PropositionalEquality
  test : ι-nat-list-rev 2 3 ≡ 4 ∷ 3 ∷ 2 ∷ []
  test = refl

fin-swap : ∀ {m n} → Fin (m + n) → Fin (n + m)
fin-swap {zero} zero = zero
fin-swap {zero} {suc n} (suc k) = suc (fin-swap {zero} {n} k)
fin-swap {suc m} {zero} zero = zero
fin-swap {suc m} {suc n} zero = zero
fin-swap {suc m} {n} (suc k) = g {n} {m} (fin-swap {m} {n} k)
  where
    g : ∀ {m n} → Fin (m + n) → Fin (m + suc n)
    g {zero} k = suc k
    g {suc m} zero = zero
    g {suc m} {n} (suc k) = suc (g {m} {n} k)

ι-fin-vec′ : (from : ℕ) → (len : ℕ) → Vec (Fin (len + from)) len
ι-fin-vec′ from len = V.map (fin-swap {from} {len}) (ι-fin-vec from len)

ι-nat-vec : (from : ℕ) → (len : ℕ) → Vec ℕ len
ι-nat-vec from len = V.map toℕ (ι-fin-vec from len) -- tabulate {len} ((_+_ from) ∘ toℕ)
  where
    open import Function

ι-fin-list : (from : ℕ) → (len : ℕ) → List (Fin (from + len))
ι-fin-list from len = toList (ι-fin-vec from len)

ι-nat-list : (from : ℕ) → (len : ℕ) → List ℕ
ι-nat-list from len = toList (ι-nat-vec from len)

{-

…-lemma : ∀ m n → m …↓ n ≡ reverse (n … m)
…-lemma zero zero = refl
…-lemma zero (suc n) = begin
  downFromLenℕ zero (0 ∸ n)
    ≡⟨ cong (downFromLenℕ zero) (0∸n≡0 n) ⟩
  reverse []
    ≡⟨ cong reverse (sym (begin
      fromLenℕ (suc n) (0 ∸ n)
        ≡⟨ cong (fromLenℕ (suc n)) (0∸n≡0 n) ⟩
    [] ∎)) ⟩
  reverse (suc n … zero) ∎
    where
      0∸n≡0 : ∀ n → 0 ∸ n ≡ 0
      0∸n≡0 zero    = refl
      0∸n≡0 (suc n) = refl

  …-lemma (suc m) n = {!!}

-}
