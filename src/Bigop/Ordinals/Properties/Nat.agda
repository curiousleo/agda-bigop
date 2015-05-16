module Bigop.Ordinals.Properties.Nat where

open import Bigop.DecidableEquality
open import Bigop.Ordinals.Nat
open import Bigop.Filter

open import Data.List.Base
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin hiding (_+_; _<_; _≤_; lift)
open import Data.Fin.Properties using (toℕ-fromℕ≤)
open import Data.Nat.Base
open import Data.Nat.Properties.Simple
open import Data.Product hiding (map)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning

suc-lemma : ∀ m n → map suc (upFrom m n) ≡ upFrom (suc m) n
suc-lemma m zero    = refl
suc-lemma m (suc n) = cong (_∷_ (suc m)) (suc-lemma (suc m) n)

range-suc : ∀ m n → map suc (range m n) ≡ range (suc m) (suc n)
range-suc m n = suc-lemma m (n ∸ m)

suc-head-lemma : ∀ m n → m ∷ (upFrom (suc m) n) ≡ upFrom m (suc n)
suc-head-lemma m n = refl

suc-last-lemma : ∀ m n → upFrom m (suc n) ≡ (upFrom m n) ∷ʳ (m + n)
suc-last-lemma m zero = cong (_∷ʳ_ []) $ +-comm zero m
suc-last-lemma m (suc n) = begin
  m ∷ upFrom (suc m) (suc n)
    ≡⟨ cong (_∷_ m) $ suc-last-lemma (suc m) n ⟩
  m ∷ (upFrom (suc m) n) ∷ʳ suc m + n
    ≡⟨ cong (_∷ʳ_ $ upFrom m (suc n)) $ sym $ +-suc m n ⟩
  upFrom m (suc n) ∷ʳ m + suc n ∎

private
  ordinals-suc : ∀ m n k → k < m → upFrom m n ∥ (≟N k) ≡ []
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

ordinals-filter : ∀ m n k → m ≤ k → (k<m+n : k < (m + n)) →
                   upFrom m n ∥ (≟N k) ≡ [ k ]
ordinals-filter zero zero k z≤n ()
ordinals-filter zero (suc n) zero z≤n (s≤s z≤n) = cong (_∷_ zero) (ordinals-suc 1 n 0 (s≤s z≤n))
ordinals-filter zero (suc n) (suc k) z≤n (s≤s k<m+n) = ordinals-filter 1 n (suc k) (s≤s z≤n) (s≤s k<m+n)
ordinals-filter (suc m) n zero () k<m+n
ordinals-filter (suc m) zero (suc k) (s≤s m≤k) (s≤s k<m+n) rewrite +-comm m zero = ⊥-elim (contr k<m+n m≤k)
  where
    contr : ∀ {m k} → suc k ≤ m → m ≤ k → ⊥
    contr {zero} {k} () m≤k
    contr {suc m} {zero} (s≤s k+1≤m) ()
    contr {suc m} {suc k} (s≤s k+1≤m) (s≤s m≤k) = contr k+1≤m m≤k

ordinals-filter (suc m) (suc n) (suc k) (s≤s m≤k) (s≤s k<m+n) with ≟N k m
ordinals-filter (suc m) (suc n) (suc .m) (s≤s m≤k) (s≤s k<m+n) | yes refl = cong (_∷_ (suc m)) (ordinals-suc (suc (suc m)) n (suc m) (s≤s (s≤s m≤k)))
ordinals-filter (suc m) (suc n) (suc k) (s≤s m≤k) (s≤s k<m+n) | no ¬p rewrite +-suc m n = ordinals-filter (suc (suc m)) n (suc k) (s≤s (lt m k m≤k ¬p)) (s≤s k<m+n)
  where
    suc-lem : ∀ {m n} → ¬ suc m ≡ suc n → ¬ m ≡ n
    suc-lem ¬eq refl = ¬eq refl

    lt : ∀ m k → m ≤ k → ¬ k ≡ m → suc m ≤ k
    lt zero zero z≤n ¬k≡m = ⊥-elim (¬k≡m refl)
    lt (suc m) zero () ¬k≡m
    lt zero (suc k) z≤n ¬k≡m = s≤s z≤n
    lt (suc m) (suc k) (s≤s m≤k) ¬k≡m = s≤s (lt m k m≤k (suc-lem ¬k≡m))
