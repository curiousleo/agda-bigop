module Prototypes.SimpleProofs where

  open import Prototypes.BigopBijection

  open import Function using (id)
  
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
          ≡⟨ lemma₀ {suc n} ⟩
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

        open import Data.Vec.Properties

        lemma₀ : ∀ {m} → expr (suc m) ≡ m + expr m
        lemma₀ {zero} = refl
        lemma₀ {suc m}
          rewrite
            sym (tabulate-∘ {m} toℕ Data.Fin.suc)
          | sym (tabulate-∘ {m} toℕ (Data.Fin.suc ∘ suc))
          = cong suc (lem {m} suc)
          where
            sucℕ = Data.Nat.suc

            lem : ∀ {m} (f : ℕ → ℕ) →
                  sum (tabulate {m} (suc ∘ f ∘ toℕ)) ≡
                  m + sum (tabulate {m} (f ∘ toℕ))
            lem {zero} f = refl
            lem {suc m} f
              rewrite
                lem {m} (f ∘ suc)
              | sym (assoc (f 0) m (sum (tabulate {m} (f ∘ sucℕ ∘ toℕ))))
              | +-comm (f 0) m
              | sym (assoc m (f 0) (sum (tabulate {m} (f ∘ sucℕ ∘ toℕ))))
              = refl

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

--  syntax innerBigop ⟦ (λ x → e) ⟧ = Σ x 〖 e 〗 -- or ⨁

    A×〈B×C〉 : Fin p → Fin s → ℕ
    A×〈B×C〉 = λ i j → outerBigop
      ⟦ (λ k → A [ i , k ] * (innerBigop
        ⟦ (λ l → B [ k , l ] * C [ l , j ]) ⟧)) ⟧
{-
    = λ i j → Σ k 〖 A [ i , k ] * Σ l 〖 B [ k , l ] * C [ l , j ] 〗 〗
-}

    〈A×B〉×C : Fin p → Fin s → ℕ
    〈A×B〉×C = λ i j → innerBigop
      ⟦ (λ l → (outerBigop
        ⟦ (λ k → A [ i , k ] * B [ k , l ]) ⟧)
        * C [ l , j ]) ⟧
{-
    = λ i j → Σ l 〖 Σ k 〖 A [ i , k ] * B [ k , l ] 〗 * C [ l , j ] 〗
-}
    eq : ∀ {i j} → A×〈B×C〉 i j ≡ 〈A×B〉×C i j
    eq {i} {j} =
      begin
        A×〈B×C〉 i j
          ≡⟨ {!!} ⟩
        〈A×B〉×C i j
{-
        Σ k 〖 A [ i , k ] * Σ l 〖 B [ k , l ] * C [ l , j ] 〗 〗
          ≡⟨ ? ⟩
        Σ k 〖 Σ l 〖 A [ i , k ] * (B [ k , l ] * C [ l , j ]) 〗 〗
          ≡⟨ ? ⟩
        Σ l 〖 Σ k 〖 A [ i , k ] * (B [ k , l ] * C [ l , j ]) 〗 〗
          ≡⟨ ? ⟩
        Σ l 〖 Σ k 〖 (A [ i , k ] * B [ k , l ]) * C [ l , j ] 〗 〗
          ≡⟨ ? ⟩
        Σ l 〖 Σ k 〖 A [ i , k ] * B [ k , l ] 〗 * C [ l , j ] 〗
-}
      ∎
      where
        open ≡-Reasoning
