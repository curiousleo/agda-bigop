module Prototypes.SimpleProofs where

  open import Prototypes.BigopBijection
  
  open import Data.Nat
  open import Data.Nat.DivMod
  open import Data.Nat.Properties.Simple
  open import Data.Fin hiding (_+_)
  open import Data.Unit.Base

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary.Decidable hiding (map)

  module Proof1 where

    bigop : ℕ → Bigop
    bigop = finSumBigop

    expr : ℕ → ℕ
    expr n = (bigop n) ⟦ toℕ ⟧

    proof : (n : ℕ) → expr (suc n) ≡ (n * (suc n)) div 2
    proof zero = refl
    proof (suc n) =
      begin
        expr (suc (suc n))
          ≡⟨ lemma₀ ⟩
        expr (suc n) + (suc n)
          ≡⟨ +-comm (expr (suc n)) (suc n) ⟩
        (suc n) + expr (suc n)
          ≡⟨ cong (_+_ (suc n)) (proof n) ⟩
        (suc n) + (n * suc n) div 2
          ≡⟨ lemma₁ {suc n} {n * suc n} ⟩
        ((suc n) + (suc n) + (n * suc n)) div 2
          ≡⟨ cong (divBy 2 {tt}) lemma₂ ⟩
        ((suc n) * suc (suc n)) div 2
      ∎
      where
        open ≡-Reasoning
        open import Data.Vec
        open import Function using (_∘_)
        open import Data.Product hiding (map)

        m : ℕ
        m = suc n

        open Bigop (bigop (suc m))
        open BigopLemmas (bigop (suc m))

        results : Vec Index (suc m)
        results = enum index

        fold·-map : fold· (map toℕ results) ≡
                    fold· (init (map toℕ results)) · toℕ (last results)
        fold·-map = fold·-map-lemmaʳ {m} results toℕ

        init-map : expr m ≡ fold· (init (map toℕ results))
        init-map = {!!}
{-
        init-map rewrite fold·-map with initLast results
        init-map | zero ∷ proj₁ , x′ , proj₃ = {!!}
        init-map | suc _ ∷ _ , _ , ()
-}

        lemma₀ : expr (suc m) ≡ expr m + m
        lemma₀ rewrite fold·-map = {!!}
     --   rewrite
     --     fold·-map-lemmaʳ {n} (enum (Bigop.index (bigop n))) toℕ
     --     = {!!}

        lemma₁ : ∀ {i j} → i + j div 2 ≡ (i + i + j) div 2
        lemma₁ {i} {j} = {!!}
          where
            lem₀ : i ≡ (i + i) div 2
            lem₀ = {!!}

        lemma₂ : (suc n) + (suc n) + (n * suc n) ≡ (suc n) * suc (suc n)
        lemma₂ = {!!}

        divBy : (divisor : ℕ) {≢0 : False (divisor ≟ 0)} (dividend : ℕ) → ℕ
        divBy n {≢0} m = _div_ m n {≢0}
