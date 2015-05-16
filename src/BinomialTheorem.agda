module BinomialTheorem where

open import Bigop

open import Algebra
open import Data.Nat.Base using (_∸_; zero; suc)
open import Data.Nat.Properties using (commutativeSemiring)
open import Data.Nat.Properties.Simple using (+-suc)
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open P.≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
import Relation.Binary.EqReasoning as EqR

open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)
module Σ = Props.SemiringWithoutOne semiringWithoutOne
open Fold +-monoid using (fold; Σ-syntax)

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
x ^ 0     = 1
x ^ suc n = x * x ^ n

_choose_ : ℕ → ℕ → ℕ
_     choose 0     = 1
0     choose suc k = 0
suc n choose suc k = n choose k + n choose (suc k)

_! : ℕ → ℕ
0 !     = 1
suc n ! = suc n * (n !)

fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

mutual

  choose-lt : ∀ m n → n choose (suc m + n) ≡ 0
  choose-lt m zero    = P.refl
  choose-lt m (suc n) = choose-lt′ m n ⟨ +-cong ⟩ choose-lt′ (suc m) n

  choose-lt′ : ∀ m n → n choose (m + suc n) ≡ 0
  choose-lt′ m n = start
    n choose (m + suc n)  ≣⟨ P.refl ⟨ P.cong₂ _choose_ ⟩ +-suc m n ⟩
    n choose suc (m + n)  ≣⟨ choose-lt m n ⟩
    0                     □

module BinomialTheorem where

  open import Data.List
  open import Data.Product using (proj₁; proj₂)

  open EqR setoid
  open import Level renaming (zero to lzero; suc to lsuc)
  open Props.Ordinals

  f : ℕ → ℕ → ℕ → ℕ
  f x n k = n choose k * x ^ k

  _…_ = rangeℕ

  infix 6 Σ-≤-syntax

  Σ-≤-syntax : (ℕ → ℕ) → ℕ → ℕ → ℕ
  Σ-≤-syntax f m n = fold f (m … suc n)
  
  syntax Σ-≤-syntax (λ x → e) m n = Σ[ m ≤ x ≤ n ] e

  map-suc : ∀ m n f g → (∀ x → f (suc x) ≈ g x) →
            Σ[ suc m ≤ k ≤ suc n ] f k ≈ Σ[ m ≤ k ≤ n ] g k
  map-suc m n f g eq = begin
    Σ[ k ← suc m … suc (suc n) ] f k
      ≈⟨ sym $ P.cong (fold f) (range-suc m (suc n)) ⟩
    Σ[ k ← map suc (m … suc n) ] f k
      ≈⟨ sym (Σ.map′ {f = g} f suc (m … suc n) (λ x x₁ → sym (eq x))) ⟩
    Σ[ m ≤ k ≤ n ] g k ∎
              -- Σ[ suc m ≤ k ≤ suc n ] e₁ = Σ[ m ≤ k ≤ n ] e₂

  split : ∀ x n → -- Σ[ 1 ≤ k ≤ suc n ] (suc n) choose k * x ^ k ≈
                  Σ[ 1 ≤ k ≤ suc n ] (suc n) choose k * x ^ k ≈
                  Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k)
                  + Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k)
  split x n = begin
    Σ[ 1 ≤ k ≤ suc n ] (suc n) choose k * x ^ k
      ≈⟨ map-suc 0 n (f x (suc n))
                     (λ k → (n choose k + n choose (suc k)) * x ^ (suc k))
                     (λ k → refl) ⟩
    Σ[ 0 ≤ k ≤ n ] (n choose k + n choose (suc k)) * x ^ (suc k)
      ≈⟨ Σ.cong {f = λ k → (n choose k + n choose (suc k)) * x ^ (suc k)}
                (0 … suc n) P.refl
                (λ k → distribʳ (x ^ (suc k)) (n choose k) _) ⟩
    Σ[ 0 ≤ k ≤ n ] (n choose k * x ^ (suc k)
                        + n choose (suc k) * x ^ (suc k))
      ≈⟨ sym $ Σ.merge (λ k → n choose k * x ^ (suc k)) (λ k → f x n (suc k))
                       (0 … suc n) ⟩
    Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k)
        + Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k) ∎

  +-reorder : ∀ x y z → x + (y + z) ≈ y + (x + z)
  +-reorder x y z = begin
    x + (y + z)  ≈⟨ sym $ +-assoc x y z ⟩
    (x + y) + z  ≈⟨ +-cong (+-comm x y) refl ⟩
    (y + x) + z  ≈⟨ +-assoc y x z ⟩
    y + (x + z)  ∎

  *-reorder : ∀ x y z → x * (y * z) ≈ y * (x * z)
  *-reorder x y z = begin
    x * (y * z)  ≈⟨ sym $ *-assoc x y z ⟩
    (x * y) * z  ≈⟨ *-cong (*-comm x y) refl ⟩
    (y * x) * z  ≈⟨ *-assoc y x z ⟩
    y * (x * z)  ∎

  left-distr : ∀ x n → Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k) ≈ x * (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k)
  left-distr x n = begin
    Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k)  ≈⟨ Σ.cong (0 … suc n) P.refl (λ k → *-reorder (n choose k) x (x ^ k)) ⟩
    Σ[ 0 ≤ k ≤ n ] x * (n choose k * x ^ k)  ≈⟨ sym $ Σ.distrˡ (f x n) x (0 … suc n) ⟩
    x * (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k)  ∎

  choose-suc : ∀ x n → Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k) ≈ Σ[ 1 ≤ k ≤ n ] n choose k * x ^ k
  choose-suc x n  = begin
    Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k)
      ≈⟨ sym $ map-suc 0 n (f x n) (f x n ∘ suc) (λ k → refl) ⟩
    Σ[ 1 ≤ k ≤ suc n ] n choose k * x ^ k           ≡⟨ P.cong (fold $ f x n) (suc-last-lemma 1 n) ⟩
    Σ[ k ← (1 … suc n) ∷ʳ (suc n) ] n choose k * x ^ k  ≈⟨ Σ.last (f x n) (suc n) (1 … suc n) ⟩
    (Σ[ 1 ≤ k ≤ n ] n choose k * x ^ k) + n choose (suc n) * x ^ (suc n)
      ≈⟨ +-cong (refl {x = Σ[ 1 ≤ k ≤ n ] f x n k})
                (choose-lt 0 n ⟨ *-cong ⟩ refl ⟨ trans ⟩ zeroˡ n) ⟩
    (Σ[ 1 ≤ k ≤ n ] n choose k * x ^ k) + 0         ≈⟨ proj₂ +-identity _ ⟩
    Σ[ 1 ≤ k ≤ n ] n choose k * x ^ k               ∎

  shift : ∀ x n → 1 + Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k)
          ≈ Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k
  shift x n = begin
    1 + Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k)  ≈⟨ (refl {x = 1}) ⟨ +-cong ⟩  (choose-suc x n) ⟩
    Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k                  ∎

  proof : ∀ x n → Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k ≈ (suc x) ^ n
  proof x zero    = refl
  proof x (suc n) = begin
    1 + Σ[ 1 ≤ k ≤ suc n ] (suc n) choose k * x ^ k        ≈⟨ refl {x = 1} ⟨ +-cong ⟩ (split x n) ⟩
    1 + (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k)
         + Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k))
                                                           ≈⟨ +-reorder 1 (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k)) _ ⟩
    Σ[ 0 ≤ k ≤ n ] n choose k * x ^ (suc k)
    + (1 + Σ[ 0 ≤ k ≤ n ] n choose (suc k) * x ^ (suc k))  ≈⟨ left-distr x n ⟨ +-cong ⟩ shift x n ⟩
      x * (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k)
    +      Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k               ≈⟨ refl {x = x * _} ⟨ +-cong ⟩ sym (proj₁ *-identity _) ⟩
      x * (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k)
    + 1 * (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k)              ≈⟨ sym $ distribʳ _ x 1 ⟩
    (x + 1) * (Σ[ 0 ≤ k ≤ n ] n choose k * x ^ k)          ≈⟨ +-comm x 1 ⟨ *-cong ⟩ proof x n ⟩
    (suc x) ^ (suc n) ∎

{-
module RowSum where

  _…+_ = upFromℕ

  proof : ∀ m r → Σ[ k ← 0 …+ m ] (2 + r) choose k * (r * k) ≈ m * (2 + r) choose m
  proof zero    r = refl
  proof (suc m) r = {!!}
-}

{-
module PascalDiagonal where

  _…+_ = upFromℕ

  proof : ∀ n → Σ[ k ← 0 …+ n ] (n ∸ k) choose k ≡ fib n
  proof zero          = refl
  proof (suc zero)    = refl
  proof (suc (suc n)) =
    begin
      Σ[ k ← 0 …+ (suc (suc n)) ] (suc (suc n) ∸ k) choose k
        ≡⟨ {!!} ⟩
      fib n + fib (suc n)
    ∎
    where
      open P.≡-Reasoning
-}
