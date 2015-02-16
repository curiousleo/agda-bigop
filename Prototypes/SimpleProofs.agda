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

        OpS = (bigop (suc m))
        Op = (bigop m)
        open BigopLemmas OpS

        results : Vec (Bigop.Index OpS) (suc m)
        results = enum (Bigop.index OpS)
{-
        fold·-map : fold· (map toℕ results) ≡
                    fold· (init (map toℕ results)) · toℕ (last results)
        fold·-map = fold·-map-lemmaʳ {m} results toℕ

        init-map : ∀ {k} →
                  (bigop (suc k)) ⟦ toℕ ⟧ ≡
                  fold· (init (map toℕ (enum (Bigop.index (bigop (suc k))))))
        init-map {zero} = refl
        init-map {suc k} = {!!}

        init-map {zero} = refl
        init-map {suc m} with initLast (enum (Bigop.index (bigop (suc (suc m)))))
        init-map {suc m} | zero ∷ xs′ , x′ , eq = {!eq!}
        init-map {suc m} | suc _ ∷ _ , _ , ()

        init-map rewrite fold·-map with initLast results
        init-map | zero ∷ proj₁ , x′ , proj₃ = {!!}
        init-map | suc _ ∷ _ , _ , ()
-}
        open import Data.Vec.Properties

        lem₁ : ∀ {m} → (f : ∀ {m} → Fin m → ℕ) →
               map toℕ (enum (Bigop.index (bigop (suc m)))) ≡
               map toℕ (enum (Bigop.index (bigop m))) ∷ʳ m
        lem₁ {zero} f = refl
        lem₁ {suc m} f = {!!}

        lemma₀ : ∀ {m} → expr (suc m) ≡ expr m + m
        lemma₀ {m}
          rewrite
            lem₁ {m} toℕ = {!!}
{-        rewrite
            foldl-foldr 0 (map toℕ (enum (Bigop.index (bigop m))))
          | foldl·-pickʳ m 0 (map toℕ (enum (Bigop.index (bigop m))))
          | sym (foldl-foldr 0 (map toℕ (enum (Bigop.index (bigop m))) ∷ʳ m))
          = {!refl!}
-}
        lem : ∀ {m} → map toℕ (enum (Bigop.index (bigop (suc m)))) ≡
                      0 ∷ map (suc ∘ toℕ) (enum (Bigop.index (bigop m)))
        lem {zero} = refl
        lem {suc m} rewrite lem {m} = cong (_∷_ zero) {!!}
{-
            foldl-foldr 0 (map toℕ (enum (Bigop.index (bigop (suc (suc m))))))
          | foldl-foldr 0 (map toℕ (enum (Bigop.index (bigop (suc m)))))
          | foldl·-distr (suc m) 0 (map toℕ (enum (Bigop.index (bigop (suc m))))) = {!refl!}
-}
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

  open import Prototypes.Matrix

  module Proof2 {p q r s}
                (A : Matrix ℕ p q) (B : Matrix ℕ q r) (C : Matrix ℕ r s) where
    _⊗_ : ∀ {p q r ℓ} {T : Set ℓ} → Matrix T p q → Matrix T q r → Matrix T p r
    m₁ ⊗ m₂ = tabulate (λ r c → {!!})

    innerBigop = finSumBigop r
    outerBigop = finSumBigop q

    A×〈B×C〉 : Fin p → Fin s → ℕ
    A×〈B×C〉 = λ i j → outerBigop
      ⟦ (λ k → lookup i k A * (innerBigop
        ⟦ (λ l → (lookup k l B) * (lookup l j C)) ⟧)) ⟧

    〈A×B〉×C : Fin p → Fin s → ℕ
    〈A×B〉×C = λ i j → innerBigop
      ⟦ (λ l → (outerBigop
        ⟦ (λ k → (lookup i k A) * (lookup k l B)) ⟧)
        * (lookup l j C)) ⟧

    eq : A×〈B×C〉 ≡ 〈A×B〉×C
    eq = {!!}
