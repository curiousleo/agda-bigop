module Prototypes.BigopFoldProofs where

  open import Prototypes.BigopFold

  open import Algebra

  open import Function

  open import Data.Unit hiding (setoid)
  open import Data.Vec hiding (sum)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.EqReasoning as EqR

  module GaussFormula where

    0… = fromZeroℕ

    open import Data.Nat.Properties using (commutativeSemiring)
    open import Algebra using (CommutativeSemiring)
    open CommutativeSemiring commutativeSemiring hiding (_+_; _*_)
    open Core +-monoid using (Σ-syntax)

    open import Data.Nat hiding (fold)

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

  module MatrixSumAssoc {p q}
         {c ℓ} (S : Semigroup c ℓ)
         (A : Matrix (Semigroup.Carrier S) p q)
         (B : Matrix (Semigroup.Carrier S) p q)
         (C : Matrix (Semigroup.Carrier S) p q) where

    open import Data.Fin hiding (_+_; fold)
    0… = fromZeroFin

    open Semigroup S renaming (Carrier to R; _∙_ to _+_)

    A+[B+C] : Fin p → Fin q → R
    A+[B+C] i j = A [ i , j ] + (B [ i , j ] + C [ i , j ])

    [A+B]+C : Fin p → Fin q → R
    [A+B]+C i j = (A [ i , j ] + B [ i , j ]) + C [ i , j ]

    proof : ∀ {i j} → A+[B+C] i j ≈ [A+B]+C i j
    proof {i} {j} = sym (assoc (A [ i , j ]) (B [ i , j ]) (C [ i , j ]))

  module MatrixMulAssoc {p q r s}
         {c ℓ} (S : CommutativeSemiringWithoutOne c ℓ)
         (A : Matrix (CommutativeSemiringWithoutOne.Carrier S) p q)
         (B : Matrix (CommutativeSemiringWithoutOne.Carrier S) q r)
         (C : Matrix (CommutativeSemiringWithoutOne.Carrier S) r s) where

    open import Data.Fin hiding (_+_; fold)

    0… = fromZeroFin

    open CommutativeSemiringWithoutOne S renaming (Carrier to R)

    open SemiringWithoutOneLemmas semiringWithoutOne
    open CommutativeMonoidLemmas +-commutativeMonoid
    open MonoidLemmas +-monoid

    open Core +-monoid using (Σ-syntax)

    A×[B×C] : Fin p → Fin s → R
    A×[B×C] i j = Σ[ k ← 0… q $ A [ i , k ] * Σ[ l ← 0… r $ B [ k , l ] * C [ l , j ] ] ]

    [A×B]×C : Fin p → Fin s → R
    [A×B]×C i j = Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ] ]
    
    proof : ∀ {i j} → A×[B×C] i j ≈ [A×B]×C i j
    proof {i} {j} =
      begin
        Σ[ k ← 0… q $ A [ i , k ] * Σ[ l ← 0… r $ B [ k , l ] * C [ l , j ] ] ]
          ≈⟨ Σ-cong lemma₀ (0… q) ⟩
        Σ[ k ← 0… q $ Σ[ l ← 0… r $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ] ]
          ≈⟨ Σ-swap (λ k l → A [ i , k ] * (B [ k , l ] * C [ l , j ]))
                    (0… q) (0… r) ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ] ]
          ≈⟨ Σ-cong (λ l → Σ-cong (lemma₁ l) (0… q)) (0… r) ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ (A [ i , k ] * B [ k , l ]) * C [ l , j ] ] ]
          ≈⟨ Σ-cong lemma₂ (0… r) ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ] ]
      ∎
      where
        open EqR setoid

        lemma₀ : ∀ k →
                 A [ i , k ] * Σ[ l ← 0… r $ B [ k , l ] * C [ l , j ] ] ≈
                 Σ[ l ← 0… r $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ]
        lemma₀ k = Σ-distrˡ (λ l → B [ k , l ] * C [ l , j ])
                            (A [ i , k ]) (0… r)

        lemma₁ : ∀ l k →
                 A [ i , k ] * (B [ k , l ] * C [ l , j ]) ≈
                 (A [ i , k ] * B [ k , l ]) * C [ l , j ]
        lemma₁ l k = sym $ *-assoc (A [ i , k ]) (B [ k , l ]) (C [ l , j ])

        lemma₂ : ∀ l →
                 Σ[ k ← 0… q $ (A [ i , k ] * B [ k , l ]) * C [ l , j ] ] ≈
                 Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ]
        lemma₂ l = begin
          Σ[ k ← 0… q $ (A [ i , k ] * B [ k , l ]) * C [ l , j ] ]
            ≈⟨ Σ-cong (λ k → *-comm (A [ i , k ] * B [ k , l ])
                                    (C [ l , j ]))
                      (0… q) ⟩
          Σ[ k ← 0… q $ C [ l , j ] * (A [ i , k ] * B [ k , l ]) ]
            ≈⟨ sym $ Σ-distr (λ k → A [ i , k ] * B [ k , l ])
                             (C [ l , j ]) (0… q) ⟩
          C [ l , j ] * Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ]
            ≈⟨ *-comm (C [ l , j ]) _ ⟩
          Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ] ∎
