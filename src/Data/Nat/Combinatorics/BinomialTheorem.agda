--
-- BinomialTheorem.agda, a module culminating in a proof of the binomial theorem,
-- in the function binomial-theorem.
--
--

module Data.Nat.Combinatorics.BinomialTheorem where

open import Bigop
open Props.Interval.Nat
open import Bigop.Interval.Nat

open import Algebra

open import Data.List

open import Data.Nat.Base
  using (_∸_; zero; suc)

open import Data.Nat.Combinatorics.Combinatorics

open import Data.Nat.Properties
  using (commutativeSemiring)
open import Data.Nat.Properties.Simple
  using (+-suc)

open import Data.Product
  using (proj₁; proj₂)

open import Function

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality as P
  using (_≡_)
open P.≡-Reasoning

open CommutativeSemiring commutativeSemiring
--  hiding (sym; refl; trans)
  renaming (Carrier to ℕ)

module Σ = Props.SemiringWithoutOne semiringWithoutOne

open Fold +-monoid
  using (fold; Σ-syntax)
open RequiresMonoid *-monoid

-- Shorthand so that we don't have to keep writing out the full expression…
f : ℕ → ℕ → ℕ → ℕ
f x n k = n choose k * x ^ k

split : ∀ x n →
  (Σ[ k ← 1 to suc n ] (suc n) choose k * x ^ k) ≡
    (Σ[ k ← 0 to n ] n choose k * x ^ (suc k)) + (Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k))
split x n =
  begin
    Σ[ k ← 1 to suc n ] (suc n) choose k * x ^ k
       ≡⟨ sym $ P.cong (fold (f x (suc n))) (upFrom-suc 0 (suc n)) ⟩
    Σ[ k ← map suc (0 to n) ] (suc n) choose k * x ^ k
       ≡⟨ sym (Σ.map′ (f x (suc n)) suc (0 to n) (λ _ _ → refl)) ⟩       
    Σ[ k ← 0 to n ] ((n choose k + n choose (suc k)) * x ^ (suc k))
       ≡⟨ Σ.cong {f = λ k → (n choose k + n choose (suc k)) * x ^ (suc k)}       
               (0 to n) P.refl (λ k → distribʳ (x ^ (suc k)) (n choose k) _) ⟩          
    Σ[ k ← 0 to n ] ((n choose k * x ^ (suc k)) + n choose (suc k) * x ^ (suc k))
       ≡⟨ sym $ Σ.∙-distr (λ k → n choose k * x ^ (suc k)) (λ k → f x n (suc k)) (0 to n) ⟩
    (Σ[ k ← 0 to n ] n choose k * x ^ (suc k)) + (Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k))
  ∎


+-reorder : ∀ x y z → x + (y + z) ≡ y + (x + z)
+-reorder x y z =
  begin
    x + (y + z)
      ≡⟨ sym $ +-assoc x y z ⟩
    (x + y) + z
      ≡⟨ +-cong (+-comm x y) refl ⟩
    (y + x) + z
      ≡⟨ +-assoc y x z ⟩
    y + (x + z)
  ∎

*-reorder : ∀ x y z → x * (y * z) ≡ y * (x * z)
*-reorder x y z =
  begin
    x * (y * z)
      ≡⟨ sym $ *-assoc x y z ⟩
    (x * y) * z
      ≡⟨ *-cong (*-comm x y) refl ⟩
    (y * x) * z
      ≡⟨ *-assoc y x z ⟩
    y * (x * z)
  ∎

left-distr : ∀ x n → Σ[ k ← 0 to n ] n choose k * x ^ (suc k) ≡ x * (Σ[ k ← 0 to n ] n choose k * x ^ k)
left-distr x n =
  begin
    Σ[ k ← 0 to n ] n choose k * x ^ (suc k)
      ≡⟨ Σ.cong (0 to n) P.refl (λ k → *-reorder (n choose k) x (x ^ k)) ⟩
    Σ[ k ← 0 to n ] x * (n choose k * x ^ k)
      ≡⟨ sym $ Σ.distrˡ (f x n) x (0 to n) ⟩
    x * (Σ[ k ← 0 to n ] n choose k * x ^ k)
  ∎

choose-suc : ∀ x n → Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k) ≡ Σ[ k ← 1 to n ] n choose k * x ^ k
choose-suc x n  =
  begin
    Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k)
      ≡⟨ Σ.map′ (f x n) suc (0 to n) (λ _ _ → refl) ⟩
    Σ[ k ← map suc (0 to n) ] n choose k * x ^ k
      ≡⟨ P.cong (fold $ f x n) (upFrom-suc 0 (suc n)) ⟩
    Σ[ k ← 1 to suc n ] n choose k * x ^ k
      ≡⟨ P.cong (fold $ f x n) (upFrom-last 1 n) ⟩
    Σ[ k ← (1 to n) ∷ʳ (suc n) ] n choose k * x ^ k
      ≡⟨ Σ.snoc (f x n) (suc n) (1 to n) ⟩
    (Σ[ k ← 1 to n ] n choose k * x ^ k) + (n choose (suc n)) * x ^ (suc n)
      ≡⟨ +-cong (refl {x = Σ[ k ← 1 to n ] f x n k}) (choose-+ 0 n ⟨ *-cong ⟩ refl ⟨ trans ⟩ zeroˡ n) ⟩
    (Σ[ k ← 1 to n ] n choose k * x ^ k) + 0
      ≡⟨ proj₂ +-identity _ ⟩
    Σ[ k ← 1 to n ] n choose k * x ^ k
  ∎
  
shift : ∀ x n →
  1 + (Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k))
      ≡ Σ[ k ← 0 to n ] n choose k * x ^ k
shift x n =
  begin
    1 + (Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k))
      ≡⟨ (refl {x = 1}) ⟨ +-cong ⟩  (choose-suc x n) ⟩
    1 + (Σ[ k ← 1 to n ] n choose k * x ^ k)
      ≡⟨ refl ⟩
    Σ[ k ← 0 ∷ (1 to n) ] n choose k * x ^ k
      ≡⟨ P.cong (fold $ f x n) (upFrom-head 0 n) ⟩
    Σ[ k ← 0 to n ] n choose k * x ^ k
  ∎

binomial-theorem : ∀ x n → Σ[ k ← 0 to n ] n choose k * x ^ k ≡ (suc x) ^ n
binomial-theorem x zero    = refl
binomial-theorem x (suc n) =
  begin
    1 + (Σ[ k ← 1 to suc n ] (suc n) choose k * x ^ k)
      ≡⟨ refl {x = 1} ⟨ +-cong ⟩ (split x n) ⟩
    1 + (Σ[ k ← 0 to n ] n choose k * x ^ (suc k)) + (Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k))
      ≡⟨ +-reorder 1 (Σ[ k ← 0 to n ] n choose k * x ^ (suc k)) _ ⟩
    (Σ[ k ← 0 to n ] n choose k * x ^ (suc k)) + (1 + (Σ[ k ← 0 to n ] n choose (suc k) * x ^ (suc k)))
      ≡⟨ left-distr x n ⟨ +-cong ⟩ shift x n ⟩
    x * (Σ[ k ← 0 to n ] n choose k * x ^ k) + (Σ[ k ← 0 to n ] n choose k * x ^ k)
      ≡⟨ refl {x = x * _} ⟨ +-cong ⟩ sym (proj₁ *-identity _) ⟩
    x * (Σ[ k ← 0 to n ] n choose k * x ^ k) + 1 * (Σ[ k ← 0 to n ] n choose k * x ^ k)
      ≡⟨ sym $ distribʳ _ x 1 ⟩
    (x + 1) * (Σ[ k ← 0 to n ] n choose k * x ^ k)
      ≡⟨ +-comm x 1 ⟨ *-cong ⟩ binomial-theorem x n ⟩
    (suc x) ^ (suc n)
  ∎

