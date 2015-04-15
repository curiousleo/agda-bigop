module Bigop.Ordinals where

open import Data.List
open import Data.Fin hiding (_≤_; _+_)
open import Data.Nat

range : ∀ {from to} → from ≤ to → List (Fin to)
range (z≤n {zero})          = []
range (z≤n {suc to})        = zero ∷ map suc (range (z≤n {to}))
range (s≤s {from} {to} f≤t) = map suc (range f≤t)

fromLenF : (from len : ℕ) → List (Fin (from + len))
fromLenF from len = range {from} {from + len} (m≤m+n from len)
  where
    open Data.Nat
    open import Data.Nat.Properties.Simple

    ≤-refl : ∀ n → n ≤ n
    ≤-refl zero    = z≤n
    ≤-refl (suc n) = s≤s (≤-refl n)

    m≤m+n : ∀ m n → m ≤ m + n
    m≤m+n zero n = z≤n
    m≤m+n (suc m) zero rewrite +-comm (suc m) zero = ≤-refl (suc m)
    m≤m+n (suc m) (suc n) = s≤s (m≤m+n m (suc n))

fromLenℕ : ℕ → ℕ → List ℕ
fromLenℕ from zero = []
fromLenℕ from (suc len) = from ∷ fromLenℕ (suc from) len

downFromLenℕ : ℕ → ℕ → List ℕ
downFromLenℕ zero       zero      = []
downFromLenℕ (suc _)    zero      = []
downFromLenℕ zero       (suc len) = [ zero ]
downFromLenℕ (suc from) (suc len) = suc from ∷ downFromLenℕ from len

_…+_ = fromLenℕ
_…-_ = downFromLenℕ

_…_ : ℕ → ℕ → List ℕ
m … n = m …+ (suc n ∸ m)

_…↓_ : ℕ → ℕ → List ℕ
m …↓ n = m …- (suc m ∸ n)

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
