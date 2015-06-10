------------------------------------------------------------------------
-- Big operator library
--
-- Properties of intervals of finite sets
------------------------------------------------------------------------

module Bigop.Interval.Properties.Fin where

open import Bigop.DecidableEquality
open import Bigop.Interval.Fin
open import Bigop.Filter

open import Data.List.Base
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin hiding (_+_; _<_; _≤_; lift)
open import Data.Fin.Properties using (toℕ-fromℕ≤)
open import Data.Nat.Base
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Properties.Simple
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning

------------------------------------------------------------------------
-- Specification for upFrom

private
  ordinals-suc : ∀ m n k → toℕ k < m → upFrom m n ∥ (≟F k) ≡ []
  ordinals-suc m zero k k<m = refl
  ordinals-suc zero (suc n) k ()
  ordinals-suc (suc m) (suc n) k k<m rewrite +-suc m n with ≟F k (fromℕ≤ {suc m} (s≤s (s≤s (m≤m+n m n))))
  ordinals-suc (suc m) (suc n) .(suc (fromℕ≤ (s≤s (m≤m+n m n)))) (s≤s k<m) | yes refl = ⊥-elim (¬lt m n k<m)
    where
      ¬lt : ∀ m n → suc (toℕ (fromℕ≤ (s≤s (m≤m+n m n)))) ≤ m → ⊥
      ¬lt zero n ()
      ¬lt (suc m) n (s≤s 1+m≤n) = ¬lt m n 1+m≤n

  ordinals-suc (suc m) (suc n) k (s≤s k<m) | no ¬p = ordinals-suc (suc (suc m)) n k (s≤s (lt k<m))
    where
      lt : ∀ {m n} → m ≤ n → m ≤ suc n
      lt {zero} m≤n = z≤n
      lt {suc m} {zero} ()
      lt {suc m} {suc n} (s≤s m≤n) = s≤s (lt m≤n)

  ordinals-filter′ : ∀ m n k → m ≤ toℕ k → (k<m+n : toℕ k < (m + n)) →
                      upFrom m n ∥ (≟F k) ≡ [ k ]
  ordinals-filter′ zero zero k m≤k ()
  ordinals-filter′ (suc m) zero zero () k<m+n
  ordinals-filter′ (suc m) zero (suc k) (s≤s m≤k) (s≤s k<m+n) rewrite +-comm m zero = ⊥-elim (contr m k k<m+n m≤k)
    where
      contr : ∀ m {i} (k : Fin i) → suc (toℕ k) ≤ m → m ≤ toℕ k → ⊥
      contr zero k () m≤k
      contr (suc m) {zero} () 1+k≤m m≤k
      contr (suc m) {suc i} zero 1+k≤m ()
      contr (suc m) {suc i} (suc k) (s≤s 1+k≤m) (s≤s m≤k) = contr m k 1+k≤m m≤k

  ordinals-filter′ zero (suc n) zero z≤n (s≤s z≤n) = cong (_∷_ zero) (ordinals-suc 1 n zero (s≤s z≤n))
  ordinals-filter′ zero (suc n) (suc k) z≤n (s≤s k<m+n) = ordinals-filter′ 1 n (suc k) (s≤s z≤n) (s≤s k<m+n)
  ordinals-filter′ (suc m) (suc n) zero () k<m+n
  ordinals-filter′ (suc m) (suc n) (suc k) m≤k k<m+n rewrite +-suc m n with ≟F k (fromℕ≤ {m} (s≤s (m≤m+n m n)))
  ordinals-filter′ (suc m) (suc n) (suc .(fromℕ≤ (s≤s (m≤m+n m n)))) (s≤s m≤k) (s≤s (s≤s k<m+n)) | yes refl = cong (_∷_ (suc (fromℕ≤ (s≤s (m≤m+n m n))))) (ordinals-suc (suc (suc m)) n (suc (fromℕ≤ (s≤s (m≤m+n m n)))) (s≤s (s≤s (lt m n))))
    where
      lt : ∀ m n → toℕ (fromℕ≤ {m} (s≤s (m≤m+n m n))) ≤ m
      lt zero    n = z≤n
      lt (suc m) n = s≤s (lt m n)

  ordinals-filter′ (suc m) (suc n) (suc k) (s≤s m≤k) (s≤s (s≤s k<m+n)) | no ¬p = ordinals-filter′ (suc (suc m)) n (suc k) (s≤s (lt m k m≤k (s≤s (m≤m+n m n)) ¬p)) (s≤s (s≤s k<m+n))
    where
      lt : ∀ m k → m ≤ toℕ k → (le : m < suc m + n) → ¬ k ≡ fromℕ≤ {m} le →
           suc m ≤ toℕ k
      lt zero    zero    z≤n       (s≤s z≤n)         ¬k≡m = ⊥-elim (¬k≡m refl)
      lt zero    (suc k) z≤n       (s≤s z≤n)         ¬k≡m = s≤s z≤n
      lt (suc m) zero    ()        m≤m+n             ¬k≡m
      lt (suc m) (suc k) (s≤s m≤k) (s≤s (s≤s m≤m+n)) ¬k≡m =
        s≤s (lt m k m≤k (s≤s m≤m+n) (λ z → ¬k≡m (cong suc z)))

-- upFrom m n contains every number from m up to but not including m + n
-- exactly once

ordinals-filter : ∀ {m n k} → m ≤ toℕ k → (k<m+n : toℕ k < (m + n)) →
                     upFrom m n ∥ (≟F k) ≡ [ k ]
ordinals-filter {m} {n} {k} = ordinals-filter′ m n k
