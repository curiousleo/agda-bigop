module Data.Nat.Combinatorics.GaussIdentity where

open import Bigop
open import Bigop.Interval.Nat
open import Bigop.Interval.Properties.Nat
open import Bigop.Filter.Properties

open import Algebra

open import Function

open import Data.List.Base
open import Data.Unit
  hiding (setoid)

open import Relation.Binary.PropositionalEquality
  using (_≡_)
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary

open import Data.Nat
  using (zero; suc; _∸_)
open import Data.Nat.Properties
  using (commutativeSemiring)
open import Data.Nat.Properties.Simple
  using (+-suc)
open import Data.Product
  using (proj₁; proj₂)

open CommutativeSemiring commutativeSemiring
  renaming (Carrier to ℕ)
open P.≡-Reasoning

open Fold +-monoid

module Σ = Props.SemiringWithoutOne semiringWithoutOne

reveal-ih : ∀ n → Σ[ i ← 0 … suc n ] i ≡ Σ[ i ← 0 … n ] i + suc n
reveal-ih n =
  begin
    Σ[ i ← 0 … suc n ] i
      ≡⟨ P.cong (fold id) (upFrom-last 1 n) ⟩
    Σ[ i ← 0 … n ∷ʳ suc n ] i
      ≡⟨ Σ.snoc id (suc n) (0 … n) ⟩
    Σ[ i ← 0 … n ] i + suc n
  ∎

gauss-identity : ∀ n → 2 * (Σ[ i ← 0 … n ] i) ≡ n * (suc n)
gauss-identity 0 = P.refl
gauss-identity (suc n) =
  begin
    2 * (Σ[ i ← 0 … suc n ] i)
      ≡⟨ P.cong (_*_ 2) (reveal-ih n) ⟩
    2 * (Σ[ i ← 0 … n ] i + suc n)
      ≡⟨ proj₁ distrib 2 (Σ[ i ← 0 … n ] i) (suc n) ⟩
    2 * (Σ[ i ← 0 … n ] i) + 2 * suc n
      ≡⟨ P.cong₂ _+_ (gauss-identity n) P.refl ⟩
    n * suc n + 2 * suc n
      ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
    2 * suc n + n * suc n
      ≡⟨ P.sym (proj₂ distrib (suc n) 2 n) ⟩
    (2 + n) * suc n
      ≡⟨ *-comm (2 + n) (suc n) ⟩
    suc n * (suc (suc n))
  ∎

odd-filter-lemma : ∀ n → 0 … suc n + suc n ∥ odd ≡ 0 … n + n ∥ odd ∷ʳ suc (n + n)
odd-filter-lemma n =
  begin
    0 … suc n + suc n ∥ odd
      ≡⟨ P.cong (flip _∥_ odd ∘ _…_ 0) (+-suc (suc n) n) ⟩
    0 … suc (suc (n + n)) ∥ odd
      ≡⟨ P.cong (flip _∥_ odd) (upFrom-last 0 (suc (suc (n + n)))) ⟩
    0 … suc (n + n) ∷ʳ suc (suc (n + n)) ∥ odd
      ≡⟨ last-no (0 … suc (n + n)) (suc (suc (n + n))) odd
                 (even→¬odd (ss-even (2n-even n))) ⟩
    0 … suc (n + n) ∥ odd
      ≡⟨ P.cong (flip _∥_ odd) (upFrom-last 0 (suc (n + n))) ⟩
    0 … n + n ∷ʳ suc (n + n) ∥ odd
      ≡⟨ last-yes (0 … n + n) (suc (n + n)) odd (even+1 (2n-even n)) ⟩
    0 … n + n ∥ odd ∷ʳ suc (n + n)
  ∎

odd-gauss-identity : ∀ n → Σ[ i ← 0 … n + n ∥ odd ] i ≡ n * n
odd-gauss-identity zero    = P.refl
odd-gauss-identity (suc n) =
  begin
    Σ[ i ← 0 … suc n + suc n ∥ odd ] i
       ≡⟨ P.cong (fold id) (odd-filter-lemma n)⟩
    Σ[ i ← 0 … n + n ∥ odd ∷ʳ suc (n + n) ] i
       ≡⟨ Σ.snoc id (suc (n + n)) (0 … n + n ∥ odd) ⟩
    Σ[ i ← 0 … n + n ∥ odd ] i + suc (n + n)
       ≡⟨ +-cong (odd-gauss-identity n) refl ⟩
    n * n + suc (n + n)
      ≡⟨ +-cong (refl {x = n * n}) (sym (+-suc n n)) ⟩
    n * n + (n + suc n)
      ≡⟨ sym $ +-assoc (n * n) n (suc n) ⟩
    (n * n + n) + suc n
      ≡⟨ +-cong (+-comm (n * n) _) refl ⟩
    suc n * n + suc n
      ≡⟨ +-comm (suc n * n) _ ⟩
    suc n + suc n * n
      ≡⟨ +-cong (refl {x = suc n}) (*-comm (suc n) n) ⟩
    suc n * suc n
  ∎
