module GaussProofs where

  open import Bigop

  open import Algebra

  open import Function

  open import Data.List.Base
  open import Data.Unit hiding (setoid)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P

  module GaussFormula where

    open import Data.Nat using (suc; _∸_)
    open import Data.Nat.Properties using (commutativeSemiring)
    open import Data.Product using (proj₁; proj₂)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    module Σ = Props.SemiringWithoutOne semiringWithoutOne
    open import Bigop.Interval.Nat

    open Fold +-monoid using (fold; Σ-syntax)
    open P.≡-Reasoning

    open Props.Interval.Nat

    proof : ∀ n → 2 * (Σ[ i ← 0 to n ] i) ≡ n * (suc n)
    proof 0 = P.refl
    proof (suc n) =
      begin
        2 * (Σ[ i ← 0 to suc n ] i)          ≡⟨ P.cong (_*_ 2) lemma ⟩
        2 * ((Σ[ i ← 0 to n ] i) + suc n)    ≡⟨ proj₁ distrib 2 (Σ[ i ← 0 to n ] i) (suc n) ⟩
        2 * (Σ[ i ← 0 to n ] i) + 2 * suc n  ≡⟨ P.cong₂ _+_ (proof n) P.refl ⟩
        n * suc n + 2 * suc n                ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
        2 * suc n + n * suc n                ≡⟨ P.sym (proj₂ distrib (suc n) 2 n) ⟩
        (2 + n) * suc n                      ≡⟨ *-comm (2 + n) (suc n) ⟩
        suc n * (suc (suc n))
      ∎
      where
        lemma : Σ[ i ← 0 to suc n ] i ≡ (Σ[ i ← 0 to n ] i) + suc n
        lemma =
          begin
            Σ[ i ← 0 to suc n ] i       ≡⟨ P.cong (fold id) (upFrom-last 1 n) ⟩
            Σ[ i ← 0 to n ∷ʳ suc n ] i  ≡⟨ Σ.snoc id (suc n) (0 to n) ⟩
            (Σ[ i ← 0 to n ] i) + suc n
          ∎

  module OddGauss where

    open import Data.Nat.Properties.Simple using (+-suc)
    open import Data.List.Base
    open import Data.Empty
    open import Relation.Nullary.Decidable

    open import Data.Nat.Base hiding (fold)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring hiding (_+_; _*_)

    module Σ = Props.SemiringWithoutOne semiringWithoutOne
    open import Bigop.Interval.Nat

    open Fold +-monoid using (fold; Σ-syntax)
    open P.≡-Reasoning
    open Props.Interval.Nat
    open Props.Filter

    open import Relation.Unary

    lemma : ∀ n → 0 to (suc n + suc n) ∥ odd ≡
                  0 to (n + n) ∥ odd ∷ʳ suc (n + n)
    lemma n =
      begin
        0 to (suc n + suc n) ∥ odd
          ≡⟨ P.cong (flip _∥_ odd ∘ _to_ 0) (+-suc (suc n) n) ⟩
        0 to suc (suc (n + n)) ∥ odd
          ≡⟨ P.cong (flip _∥_ odd) (upFrom-last 0 (suc (suc (n + n)))) ⟩
        0 to suc (n + n) ∷ʳ suc (suc (n + n)) ∥ odd
          ≡⟨ last-no (0 to suc (n + n)) (suc (suc (n + n))) odd
                     (even→¬odd (ss-even (2n-even n))) ⟩
        0 to suc (n + n) ∥ odd
          ≡⟨ P.cong (flip _∥_ odd) (upFrom-last 0 (suc (n + n))) ⟩
        0 to (n + n) ∷ʳ suc (n + n) ∥ odd
          ≡⟨ last-yes (0 to (n + n)) (suc (n + n)) odd (even+1 (2n-even n)) ⟩
        0 to (n + n) ∥ odd ∷ʳ suc (n + n)
      ∎

    proof : ∀ n → Σ[ i ← 0 to (n + n) ∥ odd ] i ≡ n * n
    proof zero = P.refl
    proof (suc n) =
      begin
        Σ[ i ← 0 to (suc n + suc n) ∥ odd ] i
          ≡⟨ P.cong (fold id) (lemma n)⟩
        Σ[ i ← 0 to (n + n) ∥ odd ∷ʳ suc (n + n) ] i
          ≡⟨ Σ.snoc id (suc (n + n)) (0 to (n + n) ∥ odd) ⟩
        (Σ[ i ← 0 to (n + n) ∥ odd ] i) + suc (n + n)
          ≡⟨ +-cong (proof n) refl ⟩

        n * n + suc (n + n)  ≡⟨ +-cong (refl {x = n * n}) (sym (+-suc n n)) ⟩
        n * n + (n + suc n)  ≡⟨ sym $ +-assoc (n * n) n (suc n) ⟩
        (n * n + n) + suc n  ≡⟨ +-cong (+-comm (n * n) _) refl ⟩
        suc n * n + suc n    ≡⟨ +-comm (suc n * n) _ ⟩
        suc n + suc n * n    ≡⟨ +-cong (refl {x = suc n}) (*-comm (suc n) n) ⟩
        suc n * suc n
      ∎
