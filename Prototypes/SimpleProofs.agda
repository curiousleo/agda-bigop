module Prototypes.SimpleProofs where

  open import Prototypes.BigopBijection
  
  open import Data.Nat
  open import Data.Nat.DivMod
  open import Data.Nat.Properties.Simple
  open import Data.Fin hiding (_+_)
  open import Data.Unit.Base

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary.Decidable

  module Proof1 where

    bigop : ℕ → Bigop
    bigop = finSumBigop

    expr : ℕ → ℕ
    expr n = (bigop n) ⟦ toℕ ⟧

    proof : (n : ℕ) → expr n ≡ (n * (suc n)) div 2
    proof zero = refl
    proof (suc n) =
      begin
        expr (suc n)
          ≡⟨ lemma₀ {n} ⟩
        suc n + expr n
          ≡⟨ cong (_+_ (suc n)) (proof n) ⟩
        suc n + (n * suc n) div 2
          ≡⟨ lemma₁ {suc n} {n * suc n} ⟩
        (suc n + suc n + (n * suc n)) div 2
          ≡⟨ cong (divBy 2 {tt}) lemma₂ ⟩
        (suc n * suc (suc n)) div 2
      ∎
      where
        open ≡-Reasoning
        open import Data.Vec
        open import Function using (_∘_)
        open BigopLemmas (bigop n)

        lemma₀ : ∀ {i} → expr (suc i) ≡ suc i + expr i
        lemma₀ {zero} = refl
        lemma₀ {suc j} with expr (suc j)
        ... | e = cong suc (cong suc {!!})
          where
            cℕ : _ → Set
            cℕ x = ℕ

            rℕ = replicate toℕ

            ss : ∀ {n} → Fin n → Fin (suc (suc n))
            ss x = suc (suc x)

            lem₀ : foldr cℕ _+_ 0 (rℕ ⊛ tabulate {suc j} ss)
                   ≡ suc j + foldr cℕ _+_ 0 (rℕ ⊛ tabulate {{!j!}} ss)
            lem₀ = {!!}

        lemma₁ : ∀ {i j} → i + j div 2 ≡ (i + i + j) div 2
        lemma₁ {i} {j} = {!!}
          where
            lem₀ : i ≡ (i + i) div 2
            lem₀ = {!!}

        lemma₂ : suc n + suc n + (n * suc n) ≡ suc n * suc (suc n)
        lemma₂ = {!!}

        divBy : (divisor : ℕ) {≢0 : False (divisor ≟ 0)} (dividend : ℕ) → ℕ
        divBy n {≢0} m = _div_ m n {≢0}
