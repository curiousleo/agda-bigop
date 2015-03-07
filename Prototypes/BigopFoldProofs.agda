module Prototypes.BigopFoldProofs where

  open import Prototypes.BigopFold

  open import Algebra

  open import Function

  open import Data.Unit
  open import Data.Nat
  open import Data.Vec

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P

  module GaussFormula where

    0… = fromZeroℕ

    proof : ∀ (n : ℕ) → 2 * Σ[ x ← 0… (suc n) $ x ] ≡ n * (suc n)
    proof zero = P.refl
    proof (suc n) =
      begin
        2 * Σ[ x ← 0… (suc (suc n)) $ x ]        ≡⟨ P.cong (_*_ 2) lemma₀ ⟩
        2 * (Σ[ x ← 0… (suc n) $ x ] + suc n)    ≡⟨ distribˡ 2 Σ[ x ← 0… (suc n) $ x ] (suc n) ⟩
        2 * Σ[ x ← 0… (suc n) $ x ] + 2 * suc n  ≡⟨ P.cong₂ _+_ (proof n) P.refl ⟩
        n * suc n + 2 * suc n                    ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
        2 * suc n + n * suc n                    ≡⟨ P.sym (distribʳ (suc n) 2 n) ⟩
        (2 + n) * suc n                          ≡⟨ *-comm (2 + n) (suc n) ⟩
        suc n * (suc (suc n))
      ∎
      where
        open P.≡-Reasoning

        open import Data.Nat.Properties using (commutativeSemiring)
        open import Algebra using (CommutativeSemiring)
        open CommutativeSemiring commutativeSemiring hiding (_+_; _*_)
        open MonoidFoldLemmas +-monoid id (const $ yes tt)
        open ListLemmas

        distribˡ : ∀ m n o → m * (n + o) ≡ m * n + m * o
        distribˡ m n o
          rewrite
            *-comm m n
          | *-comm m o
          | sym (distribʳ m n o)
          | *-comm (n + o) m = refl

        lemma₀ : Σ[ x ← 0… (suc (suc n)) $ x ] ≡ Σ[ x ← 0… (suc n) $ x ] + suc n
        lemma₀ = {!!} -- rewrite ∈ʳ-lemma (0… (suc n)) (suc (suc n)) tt = {!!}

  open import Prototypes.Matrix hiding (lookup; tabulate)
  open import Data.Fin

  module MatrixAssoc {p q r s}
         (A : Matrix ℕ p q) (B : Matrix ℕ q r) (C : Matrix ℕ r s) where

    0… = fromZeroFin

    A×[B×C] : Fin p → Fin s → ℕ
    A×[B×C] i j = Σ[ k ← 0… q $ A [ i , k ] * Σ[ l ← 0… r $ B [ k , l ] * C [ l , j ] ] ]

    [A×B]×C : Fin p → Fin s → ℕ
    [A×B]×C i j = Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ] ]

    proof : ∀ {i j} → A×[B×C] i j ≡ [A×B]×C i j
    proof {i} {j} =
      begin
        Σ[ k ← 0… q $ A [ i , k ] * Σ[ l ← 0… r $ B [ k , l ] * C [ l , j ] ] ]
          ≡⟨ {!Σ[ x ← fromZeroℕ q ] x * x!} ⟩
        Σ[ k ← 0… q $ Σ[ l ← 0… r $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ] ]
          ≡⟨ {!!} ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ] ]
          ≡⟨ {!!} ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ (A [ i , k ] * B [ k , l ]) * C [ l , j ] ] ]
          ≡⟨ {!!} ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ] ]
      ∎
      where
        open P.≡-Reasoning
