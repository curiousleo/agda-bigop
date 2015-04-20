module Proofs where

  open import Bigop

  open import Algebra

  open import Function

  open import Data.Unit hiding (setoid)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.EqReasoning as EqR

  module GaussSquared where

    open import Data.List.Base
    open import Data.Empty
    open import Relation.Nullary.Decidable

    open import Data.Nat.Base using (suc)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    module Σ = Props.SemiringWithoutOne semiringWithoutOne
    open Props.Ordinals

    open Fold +-monoid using (fold; Σ-syntax)
    open EqR setoid

    lemma : ∀ n → ¬ (Odd (n + n))
    lemma n = {!!}

    open import Relation.Unary

    Σ-last-yes : ∀ {ℓ} {i} {I : Set i} (f : I → ℕ) (xs : List I) (x : I) →
                 {P : Pred I ℓ} (p : Decidable P) → P x →
                 Σ[ k ← (xs ∷ʳ x) ∥ p $ f k ] ≈ Σ[ k ← xs ∥ p $ f k ] + f x
    Σ-last-yes f xs x p px = begin
      Σ[ k ← (xs ∷ʳ x) ∥ p $ f k ]  ≈⟨ P.cong (fold f) (last-yes xs x p px) ⟩
      Σ[ k ← (xs ∥ p) ∷ʳ x $ f k ]  ≈⟨ Σ.last f x (xs ∥ p) ⟩
      Σ[ k ← xs ∥ p $ f k ] + f x   ∎

    proof : ∀ n → Σ[ i ← 0 … (n + n) ∥ odd $ i ] ≈ n * n
    proof 0 = refl
    proof (suc n) with odd (suc n + suc n)
    proof (suc n) | yes last-odd = ⊥-elim (lemma (suc n) last-odd)

    proof (suc n) | no ¬last-odd = begin
      Σ[ i ← 0 … (suc n + suc n) ∥ odd $ i ]
        ≈⟨ P.cong (fold id) ➀ ⟩
      Σ[ i ← 0 … (n + suc n) ∥ odd $ i ]
        ≈⟨ P.cong (fold id) (suc-last-lemma 0 {!n + suc n!}) ⟩
      Σ[ i ← (0 … (n + n) ∷ʳ (n + suc n)) ∥ odd $ i ]
        ≈⟨ Σ-last-yes id (0 … (n + n)) (n + (suc n)) odd (2n+1-odd n) ⟩
      Σ[ i ← 0 … (n + n) ∥ odd $ i ] + (n + suc n)
        ≈⟨ proof n ⟨ +-cong ⟩ refl ⟩
      n * n + (n + suc n)
        ≈⟨ sym (+-assoc (n * n) _ _) ⟩
      (n * n + n) + suc n
        ≈⟨ +-comm (n * n) n ⟨ +-cong ⟩ refl ⟩
      (suc n * n) + suc n
        ≈⟨ +-comm (n + n * n) _ ⟩
      suc n + (suc n * n)
        ≈⟨ (P.refl {x = suc n}) ⟨ +-cong ⟩ *-comm (suc n) n ⟩
      suc n * suc n ∎

      where
        -- open import Data.Nat.Properties.Simple

        even→odd : ∀ n → Even n → Odd (suc n)
        even→odd 0 zero-even = one-odd
        even→odd (suc ._) (ss-even even) = ss-odd (even→odd _ even)

        2n+1-odd : ∀ n → Odd (n + suc n)
        2n+1-odd n = {!!}

        ➁ : ∀ n → 0 … (suc n + suc n) ≡ 0 … (n + n) ∷ʳ (n + suc n) ∷ʳ (suc n + suc n)
        ➁ 0 = P.refl
        ➁ (suc n) = {!➁ n!}

        ➀ : 0 … (suc n + suc n) ∥ odd ≡ 0 … (n + suc n) ∥ odd
        ➀ = ⓐ ⟨ P.trans ⟩ ⓑ
          where
            ⓐ : 0 … (suc n + suc n) ∥ odd ≡ (0 … (n + suc n) ∷ʳ (suc n + suc n)) ∥ odd
            ⓐ = P.cong (flip _∥_ odd) lemma′
              where
                lemma′ : 0 … (suc n + suc n) ≡ 0 … (n + suc n) ∷ʳ (suc n + suc n)
                lemma′ = suc-last-lemma 0 $ suc n + suc n

            ⓑ = last-no {P = Odd} (0 … _+_ n (suc n)) (_+_ (suc n) (suc n)) odd ¬last-odd

  module GaussFormula where

    open import Data.Nat using (suc)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    module Σ = Props.SemiringWithoutOne semiringWithoutOne

    open Fold +-monoid using (fold; Σ-syntax)

    proof : ∀ (n : ℕ) → 2 * Σ[ x ← 0 … n $ x ] ≡ n * (suc n)
    proof 0 = P.refl
    proof (suc n) =
      begin
        2 * Σ[ x ← 0 … suc n $ x ]          ≡⟨ P.cong (_*_ 2) lemma₀ ⟩
        2 * (Σ[ x ← 0 … n $ x ] + suc n)    ≡⟨ distribˡ 2 Σ[ x ← 0 … n $ x ] (suc n) ⟩
        2 * Σ[ x ← 0 … n $ x ] + 2 * suc n  ≡⟨ P.cong₂ _+_ (proof n) P.refl ⟩
        n * suc n + 2 * suc n               ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
        2 * suc n + n * suc n               ≡⟨ P.sym (distribʳ (suc n) 2 n) ⟩
        (2 + n) * suc n                     ≡⟨ *-comm (2 + n) (suc n) ⟩
        suc n * (suc (suc n))
      ∎
      where
        open P.≡-Reasoning
        open import Data.List.Base

        open Props.Ordinals

        distribˡ : ∀ m n o → m * (n + o) ≡ m * n + m * o
        distribˡ m n o
          rewrite
            *-comm m n
          | *-comm m o
          | sym (distribʳ m n o)
          | *-comm (n + o) m = refl

        lemma₀ : Σ[ x ← 0 … suc n $ x ] ≡ Σ[ x ← 0 … n $ x ] + suc n
        lemma₀ = begin
          Σ[ x ← 0 … suc n $ x ]       ≡⟨ P.cong (fold id) (suc-last-lemma 1 n) ⟩
          Σ[ x ← 0 … n ∷ʳ suc n $ x ]  ≡⟨ Σ.last id (suc n) (0 … n) ⟩
          Σ[ x ← 0 … n $ x ] + suc n   ∎
