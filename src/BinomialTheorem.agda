module BinomialTheorem where

open import Bigop

open import Algebra
open import Data.Nat.Base using (_∸_; suc)
open import Data.Nat.Properties using (commutativeSemiring)
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.EqReasoning as EqR

open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)
module Σ = Props.SemiringWithoutOne semiringWithoutOne
open Fold +-monoid using (fold; Σ-syntax)

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
x ^ 0 = 1
x ^ (suc n) = x * x ^ n

_choose_ : ℕ → ℕ → ℕ
_     choose 0     = 1
0     choose suc k = 0
suc n choose suc k = n choose k + n choose (suc k)

choose-lemma : ∀ m n → n choose ((suc m) + n) ≡ 0
choose-lemma m 0       = P.refl
choose-lemma m (suc n) = ➀ ⟨ +-cong ⟩ ➁
  where
    open P.≡-Reasoning
    
    ➀ : n choose (m + suc n) ≡ 0
    ➀ = begin
      n choose (m + suc n)
        ≡⟨ P.refl ⟨ P.cong₂ _choose_ ⟩ begin
           m + suc n
             ≡⟨ +-comm m (suc n) ⟩
           suc (n + m)
             ≡⟨ P.cong suc (+-comm n m) ⟩
           suc (m + n) ∎
        ⟩
      n choose suc (m + n)
        ≡⟨ choose-lemma m n ⟩
      0 ∎

    ➁ : n choose suc (m + suc n) ≡ 0
    ➁ = begin
      n choose suc (m + suc n)
        ≡⟨ (P.refl {x = n}) ⟨ P.cong₂ _choose_ ⟩ begin
           suc (m + suc n)
             ≡⟨ P.cong suc (+-comm m (suc n)) ⟩
           suc (suc (n + m))
             ≡⟨ P.cong (suc ∘ suc) (+-comm n m) ⟩
           suc (suc m + n) ∎
        ⟩
      n choose suc (suc m + n)
        ≡⟨ choose-lemma (suc m) n ⟩
      0 ∎

_! : ℕ → ℕ
0 !     = 1
suc n ! = suc n * (n !)

fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

module BinomialTheorem where

  open import Data.Product using (proj₁; proj₂)

  open EqR setoid
  open import Level renaming (zero to lzero; suc to lsuc)
  open Props.Ordinals

  proof : ∀ x n → Σ[ k ← 0 … n ] n choose k * x ^ k ≈ (suc x) ^ n
  proof x 0       = refl
  proof x (suc n) = begin
    1 + Σ[ k ← 1 … suc n ] (suc n) choose k * x ^ k
      ≈⟨ refl {x = 1} ⟨ +-cong ⟩ begin
        Σ[ k ← 1 … suc n ] (suc n) choose k * x ^ k
          ≈⟨ sym $ Σ.map {g = f (suc n)} suc (λ _ → refl) (0 … n)
                   ⟨ trans ⟩ P.cong (fold (f (suc n))) (suc-lemma 0 (suc n)) ⟩
        Σ[ k ← 0 … n ] (suc n) choose (suc k) * x ^ (suc k)
          ≈⟨ Σ.cong {f = λ k → f (suc n) (suc k)}
                    (0 … n) P.refl (λ _ → refl) ⟩
        Σ[ k ← 0 … n ] (n choose k + n choose (suc k)) * x ^ (suc k)
          ≈⟨ Σ.cong {f = λ k → (n choose k + n choose (suc k)) * x ^ (suc k)}
                    (0 … n) P.refl
                    (λ k → distribʳ (x ^ (suc k)) (n choose k) _) ⟩
        Σ[ k ← 0 … n ] (n choose k * x ^ (suc k)
                        + n choose (suc k) * x ^ (suc k))
          ≈⟨ sym $ Σ.split (λ k → n choose k * x ^ (suc k)) (λ k → f n (suc k))
                           (0 … n) ⟩
        Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
        + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k) ∎
      ⟩
    1 + (Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
         + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k))
      ≈⟨ +-reorder 1 (Σ[ k ← 0 … n ] n choose k * x ^ (suc k)) _ ⟩
    Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
    + (1 + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k))
      ≈⟨ ➀ ⟨ +-cong ⟩ ➁ ⟩
      x * (Σ[ k ← 0 … n ] n choose k * x ^ k)
    +      Σ[ k ← 0 … n ] n choose k * x ^ k
      ≈⟨ +-cong (refl {x = x * _})
                (sym $ proj₁ *-identity (Σ[ k ← 0 … n ] f n k)) ⟩
      x * (Σ[ k ← 0 … n ] n choose k * x ^ k)
    + 1 * (Σ[ k ← 0 … n ] n choose k * x ^ k)
      ≈⟨ sym $ distribʳ _ x 1 ⟩
    (x + 1) * (Σ[ k ← 0 … n ] n choose k * x ^ k)
      ≈⟨ *-cong (+-comm x 1) (proof x n) ⟩
    (1 + x) * (1 + x) ^ n ∎

    where

      f : ℕ → ℕ → ℕ
      f n k = n choose k * x ^ k

      +-reorder : ∀ x y z → x + (y + z) ≈ y + (x + z)
      +-reorder x y z = begin
        x + (y + z)  ≈⟨ sym $ +-assoc x y z ⟩
        (x + y) + z  ≈⟨ +-cong (+-comm x y) refl ⟩
        (y + x) + z  ≈⟨ +-assoc y x z ⟩
        y + (x + z)  ∎

      ➀ : Σ[ k ← 0 … n ] n choose k * x ^ (suc k) ≈ x * (Σ[ k ← 0 … n ] n choose k * x ^ k)
      ➀ = begin
        Σ[ k ← 0 … n ] n choose k * x ^ (suc k)  ≈⟨ Σ.cong (0 … n) P.refl reorder ⟩
        Σ[ k ← 0 … n ] x * (n choose k * x ^ k)  ≈⟨ sym $ Σ.distrˡ (f n) x (0 … n) ⟩
        x * (Σ[ k ← 0 … n ] n choose k * x ^ k)  ∎

        where

          reorder : ∀ k → n choose k * x ^ (suc k) ≈ x * (n choose k * x ^ k)
          reorder k = begin
            n choose k * (x * x ^ k)  ≈⟨ sym $ *-assoc (n choose k) _ _ ⟩
            (n choose k * x) * x ^ k  ≈⟨ *-comm (n choose k) _ ⟨ *-cong ⟩ refl ⟩
            (x * n choose k) * x ^ k  ≈⟨ *-assoc x _ _ ⟩
            x * (n choose k * x ^ k)  ∎

      open import Data.List

      ➁ : 1 + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
          ≈ Σ[ k ← 0 … n ] n choose k * x ^ k
      ➁ = begin
        1 + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
          ≈⟨ (refl {x = 1}) ⟨ +-cong ⟩ begin
            Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
              ≈⟨ Σ.map {g = f n} suc (λ k → refl) (0 … n) ⟩
            Σ[ k ← map suc (0 … n) ] n choose k * x ^ k
              ≈⟨ P.cong (fold $ f n) (suc-lemma 0 (suc n)) ⟩
            Σ[ k ← 1 … suc n ] n choose k * x ^ k
              ≈⟨ P.cong (fold $ f n) (suc-last-lemma 1 n) ⟩
            Σ[ k ← (1 … n) ∷ʳ (suc n) ] n choose k * x ^ k
              ≈⟨ Σ.last (f n) (suc n) (1 … n) ⟩
            (Σ[ k ← 1 … n ] n choose k * x ^ k) + n choose (suc n) * x ^ (suc n)
              ≈⟨ +-cong (refl {x = Σ[ k ← 1 … n ] f n k})
                        (choose-lemma 0 n ⟨ *-cong ⟩ refl ⟨ trans ⟩ zeroˡ n) ⟩
            (Σ[ k ← 1 … n ] n choose k * x ^ k) + 0
              ≈⟨ proj₂ +-identity _ ⟩
            Σ[ k ← 1 … n ] n choose k * x ^ k ∎
          ⟩
        1 + Σ[ k ← 1 … n ] n choose k * x ^ k
          ≈⟨ refl ⟩
        Σ[ k ← 0 ∷ (1 … n) ] n choose k * x ^ k
          ≈⟨ P.cong (fold $ f n) (suc-head-lemma 0 n) ⟩
        Σ[ k ← 0 … n ] n choose k * x ^ k ∎

module RowSum where

  proof : ∀ m r → Σ[ k ← 0 …+ m ] r choose k * (r ∸ 2 * k) ≈ m * r choose m
  proof 0       r = refl
  proof (suc m) r = {!!}

module PascalDiagonal where

  proof : ∀ n → Σ[ k ← 0 …+ n ] (n ∸ k) choose k ≡ fib n
  proof 0             = refl
  proof 1             = refl
  proof (suc (suc n)) =
    begin
      Σ[ k ← 0 …+ (suc (suc n)) ] (suc (suc n) ∸ k) choose k
        ≡⟨ {!!} ⟩
      fib n + fib (suc n)
    ∎
    where
      open P.≡-Reasoning
