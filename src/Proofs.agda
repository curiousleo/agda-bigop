module Proofs where

  open import Bigop

  open import Algebra

  open import Function

  open import Data.List.Base
  open import Data.Unit hiding (setoid)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.EqReasoning as EqR

  module GaussFormula where

    open import Data.Nat using (suc; _∸_)
    open import Data.Nat.Properties using (commutativeSemiring)
    open import Data.Product using (proj₁; proj₂)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    module Σ = Props.SemiringWithoutOne semiringWithoutOne
    open Props.Ordinals

    open Fold +-monoid using (fold; Σ-syntax)
    open P.≡-Reasoning

    _…_ = rangeℕ

    proof : ∀ n → 2 * (Σ[ i ← 0 … n ] i) ≡ n * (suc n)
    proof 0 = P.refl
    proof (suc n) =
      begin
        2 * (Σ[ i ← 0 … suc n ] i)          ≡⟨ P.cong (_*_ 2) lemma ⟩
        2 * (Σ[ i ← 0 … n ] i + suc n)      ≡⟨ proj₁ distrib 2 (Σ[ i ← 0 … n ] i) (suc n) ⟩
        2 * (Σ[ i ← 0 … n ] i) + 2 * suc n  ≡⟨ P.cong₂ _+_ (proof n) P.refl ⟩
        n * suc n + 2 * suc n               ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
        2 * suc n + n * suc n               ≡⟨ P.sym (proj₂ distrib (suc n) 2 n) ⟩
        (2 + n) * suc n                     ≡⟨ *-comm (2 + n) (suc n) ⟩
        suc n * (suc (suc n))
      ∎
      where
        lemma : Σ[ i ← 0 … suc n ] i ≡ Σ[ i ← 0 … n ] i + suc n
        lemma =
          begin
            Σ[ i ← 0 … suc n ] i       ≡⟨ P.cong (fold id) (suc-last-lemma 1 n) ⟩
            Σ[ i ← 0 … n ∷ʳ suc n ] i  ≡⟨ Σ.last id (suc n) (0 … n) ⟩
            Σ[ i ← 0 … n ] i + suc n
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
    open Props.Ordinals

    open Fold +-monoid using (fold; Σ-syntax)
    open P.≡-Reasoning

    open import Relation.Unary

    _…+_ = upFromℕ

    lemma : ∀ n → 0 …+ suc (suc n + suc n) ∥ odd ≡
                  0 …+ suc (n + n) ∥ odd ∷ʳ suc (n + n)
    lemma n =
      begin
        0 …+ suc (suc n + suc n) ∥ odd
          ≡⟨ P.cong (flip _∥_ odd ∘ _…+_ 0) (3suc n) ⟩
        0 …+ suc (suc (suc (n + n))) ∥ odd
          ≡⟨ P.cong (flip _∥_ odd) (suc-last-lemma 0 (suc (suc (n + n)))) ⟩
        0 …+ suc (suc (n + n)) ∷ʳ suc (suc (n + n)) ∥ odd
          ≡⟨ last-no (0 …+ (suc (suc (n + n)))) (suc (suc (n + n))) odd
                     (even→¬odd (ss-even (2n-even n))) ⟩
        0 …+ suc (suc (n + n)) ∥ odd
          ≡⟨ P.cong (flip _∥_ odd) (suc-last-lemma 0 (suc (n + n))) ⟩
        0 …+ suc (n + n) ∷ʳ suc (n + n) ∥ odd
          ≡⟨ last-yes (0 …+ suc (n + n)) (suc (n + n)) odd (even+1 (2n-even n)) ⟩
        0 …+ suc (n + n) ∥ odd ∷ʳ suc (n + n)
      ∎
      where
        3suc : ∀ n → suc (suc n + suc n) ≡ suc (suc (suc (n + n)))
        3suc n rewrite +-suc n n = P.refl


    proof : ∀ n → Σ[ i ← 0 …+ suc (n + n) ∥ odd ] i ≈ n * n
    proof zero = P.refl
    proof (suc n) =
      begin
        Σ[ i ← 0 …+ suc (suc n + suc n) ∥ odd ] i
          ≡⟨ P.cong (fold id) (lemma n)⟩
        Σ[ i ← 0 …+ suc (n + n) ∥ odd ∷ʳ suc (n + n) ] i
          ≡⟨ Σ.last id (suc (n + n)) (0 …+ suc (n + n) ∥ odd) ⟩
        Σ[ i ← 0 …+ suc (n + n) ∥ odd ] i + suc (n + n)
          ≡⟨ +-cong (proof n) refl ⟩

        n * n + suc (n + n)  ≡⟨ +-cong (refl {x = n * n}) (sym (+-suc n n)) ⟩
        n * n + (n + suc n)  ≡⟨ sym $ +-assoc (n * n) n (suc n) ⟩
        (n * n + n) + suc n  ≡⟨ +-cong (+-comm (n * n) _) refl ⟩
        suc n * n + suc n    ≡⟨ +-comm (suc n * n) _ ⟩
        suc n + suc n * n    ≡⟨ +-cong (refl {x = suc n}) (*-comm (suc n) n) ⟩
        suc n * suc n
      ∎
