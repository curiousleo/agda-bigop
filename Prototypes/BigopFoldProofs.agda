module Prototypes.BigopFoldProofs where

  open import Prototypes.BigopFold

  open import Algebra

  open import Function

  open import Data.Unit hiding (setoid)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.EqReasoning as EqR

  module GaussFormula where

    0… = fromLenℕ 0

    open import Data.Nat hiding (fold)

    open import Data.Nat.Properties using (commutativeSemiring)
    open import Algebra using (CommutativeSemiring)
    open CommutativeSemiring commutativeSemiring hiding (_+_; _*_)
    open Core +-monoid using (Σ-syntax)

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

    0… = fromLenF 0

    open import Data.Fin hiding (_+_; fold)

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

    0… = fromLenF 0

    open import Data.Fin hiding (_+_; fold)

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
          ≈⟨ Σ-cong′ lemma₀ (0… q) ⟩
        Σ[ k ← 0… q $ Σ[ l ← 0… r $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ] ]
          ≈⟨ Σ-swap (λ k l → A [ i , k ] * (B [ k , l ] * C [ l , j ]))
                    (0… q) (0… r) ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ A [ i , k ] * (B [ k , l ] * C [ l , j ]) ] ]
          ≈⟨ Σ-cong′ (λ l → Σ-cong′ (lemma₁ l) (0… q)) (0… r) ⟩
        Σ[ l ← 0… r $ Σ[ k ← 0… q $ (A [ i , k ] * B [ k , l ]) * C [ l , j ] ] ]
          ≈⟨ Σ-cong′ lemma₂ (0… r) ⟩
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
            ≈⟨ Σ-cong′ (λ k → *-comm (A [ i , k ] * B [ k , l ])
                                     (C [ l , j ]))
                      (0… q) ⟩
          Σ[ k ← 0… q $ C [ l , j ] * (A [ i , k ] * B [ k , l ]) ]
            ≈⟨ sym $ Σ-distrˡ (λ k → A [ i , k ] * B [ k , l ])
                              (C [ l , j ]) (0… q) ⟩
          C [ l , j ] * Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ]
            ≈⟨ *-comm (C [ l , j ]) _ ⟩
          Σ[ k ← 0… q $ A [ i , k ] * B [ k , l ] ] * C [ l , j ] ∎

  module Binomials where

    open import Data.Nat using (_∸_; suc)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    open SemiringWithoutOneLemmas semiringWithoutOne
    open CommutativeMonoidLemmas +-commutativeMonoid
    open MonoidLemmas +-monoid

    open Core +-monoid using (fold; Σ-syntax)

    infixr 8 _^_

    _^_ : ℕ → ℕ → ℕ
    x ^ 0 = 1
    x ^ (suc n) = x * x ^ n

    _choose_ : ℕ → ℕ → ℕ
    _     choose 0     = 1
    0     choose suc k = 0
    suc n choose suc k = n choose k + n choose (suc k)

    _! : ℕ → ℕ
    0 !     = 1
    suc n ! = suc n * (n !)

    fib : ℕ → ℕ
    fib 0             = 0
    fib 1             = 1
    fib (suc (suc n)) = fib n + fib (suc n)

    module BinomialTheorem where

      open P.≡-Reasoning
      open import Data.Product using (proj₁; proj₂)

      open RangeLemmas

      proof : ∀ x n → Σ[ k ← 0 …+ (suc n) $ n choose k * x ^ k ] ≈ (1 + x) ^ n
      proof x 0       = refl
      proof x (suc n) = begin
        1 + Σ[ k ← 1 …+ (1 + n) $ (1 + n) choose k * x ^ k ]
          ≡⟨ (P.refl {x = 1}) ⟨ +-cong ⟩ begin
            Σ[ k ← 1 …+ (1 + n) $ (1 + n) choose k * x ^ k ]
              ≡⟨ sym $ P.cong (fold (f (1 + n))) (suc-lemma 0 (suc n)) ⟩
            Σ[ k ← map suc (0 …+ (1 + n)) $ (1 + n) choose k * x ^ k ]
              ≡⟨ sym $ Σ-cong {g = f (1 + n)} suc (λ k → P.refl) (0 …+ (1 + n)) ⟩
            Σ[ k ← 0 …+ (1 + n) $ (1 + n) choose (1 + k) * x ^ (1 + k) ]
              ≡⟨ Σ-cong′ {f = λ k → f (1 + n) (1 + k)} (λ k → P.refl) (0 …+ (1 + n)) ⟩
            Σ[ k ← 0 …+ (1 + n) $ (n choose k + n choose (1 + k)) * x ^ (1 + k) ]
              ≡⟨ Σ-cong′ {f = λ k → (n choose k + n choose (1 + k)) * x ^ (1 + k)}
                         (λ k → distribʳ (x ^ (1 + k)) (n choose k) _) (0 …+ (1 + n)) ⟩
            Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k)
                                  + n choose (1 + k) * x ^ (1 + k) ]
              ≡⟨ sym $ Σ-lift {J = ℕ}
                              (λ k → n choose k * x ^ (1 + k)) (λ k → f n (1 + k))
                              (0 …+ (1 + n)) ⟩
            Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k) ]
            + Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ] ∎
          ⟩
        1 + (Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k) ]
             + Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ])
          ≡⟨ ➀ ⟩
        Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k) ]
        + (1 + Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ])
          ≡⟨ ➃ ⟨ +-cong ⟩ ➁ ⟩
          x * Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
        +     Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
          ≡⟨ +-cong (P.refl {x = x * _})
                    (sym $ proj₁ *-identity Σ[ k ← 0 …+ (1 + n) $ f n k ]) ⟩
          x * Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
        + 1 * Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
          ≡⟨ sym $ distribʳ _ x 1 ⟩
        (x + 1) * Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
          ≡⟨ *-cong (+-comm x 1) (proof x n) ⟩
        (1 + x) * (1 + x) ^ n ∎

        where

          f : ℕ → ℕ → ℕ
          f n k = n choose k * x ^ k

          open import Data.List

          ➃ : Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k) ]
              ≈ x * Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
          ➃ = begin
            Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k) ]
              ≡⟨ Σ-cong′ lemma (0 …+ (1 + n)) ⟩
            Σ[ k ← 0 …+ (1 + n) $ x * (n choose k * x ^ k) ]
              ≡⟨ sym $ Σ-distrˡ (λ k → n choose k * x ^ k) x (0 …+ (1 + n)) ⟩
            x * Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ] ∎

            where

              lemma : ∀ k → n choose k * x ^ (1 + k) ≡ x * (n choose k * x ^ k)
              lemma k = begin
                n choose k * (x * x ^ k)
                  ≡⟨ sym $ *-assoc (n choose k) _ _ ⟩
                (n choose k * x) * x ^ k
                  ≡⟨ *-comm (n choose k) _ ⟨ *-cong ⟩ P.refl ⟩
                (x * n choose k) * x ^ k
                  ≡⟨ *-assoc x _ _ ⟩
                x * (n choose k * x ^ k) ∎

          ➂ : Σ[ k ← 0 …+ (1 + n) $ (1 + n) choose (1 + k) * x ^ (1 + k) ]
              ≈ Σ[ k ← 1 …+ (1 + n) $ (1 + n) choose k * x ^ k ]
          ➂ = begin
            Σ[ k ← 0 …+ (1 + n) $ ((1 + n) choose (1 + k)) * x ^ (1 + k) ]
              ≡⟨ Σ-cong {g = λ k → (1 + n) choose k * x ^ k} suc (λ k → P.refl) (0 …+ (1 + n)) ⟩
            Σ[ k ← map suc (0 …+ (1 + n)) $ (1 + n) choose k * x ^ k ]
              ≡⟨ P.cong (fold (λ k → (1 + n) choose k * x ^ k)) (suc-lemma 0 (suc n)) ⟩
            Σ[ k ← 1 …+ (1 + n) $ (1 + n) choose k * x ^ k ] ∎

          ➀ = lemma 1
                    Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ (1 + k) ]
                    Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ]
            where

              lemma : ∀ x y z → x + (y + z) ≈ y + (x + z)
              lemma x y z = begin
                x + (y + z)
                  ≡⟨ sym $ +-assoc x y z ⟩
                (x + y) + z
                  ≡⟨ +-cong (+-comm x y) refl ⟩
                (y + x) + z
                  ≡⟨ +-assoc y x z ⟩
                y + (x + z) ∎

          ➁ : 1 + Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ]
              ≈ Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ]
          ➁ = begin
            1 + Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ]
              ≡⟨ (P.refl {x = 1}) ⟨ +-cong ⟩ begin
                Σ[ k ← 0 …+ (1 + n) $ n choose (1 + k) * x ^ (1 + k) ]
                  ≡⟨ Σ-cong {g = λ k → n choose k * x ^ k}
                            suc (λ k → P.refl) (0 …+ (1 + n)) ⟩
                Σ[ k ← map suc (0 …+ (1 + n)) $ n choose k * x ^ k ]
                  ≡⟨ P.cong (fold (λ k → n choose k * x ^ k)) (suc-lemma 0 (suc n)) ⟩
                Σ[ k ← 1 …+ (1 + n) $ n choose k * x ^ k ]
                  ≡⟨ P.cong (fold (λ k → n choose k * x ^ k)) (suc-last-lemma 1 n) ⟩
                Σ[ k ← (1 …+ n) ∷ʳ (1 + n) $ n choose k * x ^ k ]
                  ≡⟨ Σ-last (λ k → n choose k * x ^ k) (1 + n) (1 …+ n) ⟩
                Σ[ k ← 1 …+ n $ n choose k * x ^ k ] + n choose (1 + n) * x ^ (1 + n)
                  ≡⟨ +-cong (P.refl {x = Σ[ k ← 1 …+ n $ n choose k * x ^ k ]})
                            (lemma 0 n ⟨ *-cong ⟩ P.refl ⟨ P.trans ⟩ zeroˡ n) ⟩
                Σ[ k ← 1 …+ n $ n choose k * x ^ k ] + 0
                  ≡⟨ proj₂ +-identity _ ⟩
                Σ[ k ← 1 …+ n $ n choose k * x ^ k ] ∎
              ⟩
            1 + Σ[ k ← 1 …+ n $ n choose k * x ^ k ]
              ≡⟨ P.refl ⟩
            Σ[ k ← 0 ∷ (1 …+ n) $ n choose k * x ^ k ]
              ≡⟨ P.cong (fold (λ k → n choose k * x ^ k)) (suc-head-lemma 0 n) ⟩
            Σ[ k ← 0 …+ (1 + n) $ n choose k * x ^ k ] ∎

            where

              lemma : ∀ m n → n choose ((suc m) + n) ≡ 0
              lemma m 0 = P.refl
              lemma m (suc n) = ⓐ ⟨ +-cong ⟩ ⓑ
                where
                  ⓐ : n choose (m + suc n) ≡ 0
                  ⓐ = begin
                    n choose (m + suc n)
                      ≡⟨ P.refl ⟨ P.cong₂ _choose_ ⟩ begin
                        m + suc n
                          ≡⟨ +-comm m (suc n) ⟩
                        suc (n + m)
                          ≡⟨ P.cong suc (+-comm n m) ⟩
                        suc (m + n) ∎
                      ⟩
                    n choose suc (m + n)
                      ≡⟨ lemma m n ⟩
                    0 ∎

                  ⓑ : n choose suc (m + suc n) ≡ 0
                  ⓑ = begin
                    n choose suc (m + suc n)
                      ≡⟨ (P.refl {x = n}) ⟨ P.cong₂ _choose_ ⟩ begin
                        suc (m + suc n)
                          ≡⟨ P.cong suc (+-comm m (suc n)) ⟩
                        suc (suc (n + m))
                          ≡⟨ P.cong (suc ∘ suc) (+-comm n m) ⟩
                        suc (suc m + n) ∎
                      ⟩
                    n choose suc (suc m + n)
                      ≡⟨ lemma (suc m) n ⟩
                    0 ∎

    module RowSum where

      proof : ∀ m r → Σ[ k ← 0 …+ m $ r choose k * (r ∸ 2 * k) ] ≈ m * r choose m
      proof 0       r = refl
      proof (suc m) r = {!!}

    module PascalDiagonal where

      proof : ∀ n → Σ[ k ← 0 …+ n $ (n ∸ k) choose k ] ≡ fib n
      proof 0             = refl
      proof 1             = refl
      proof (suc (suc n)) =
        begin
          Σ[ k ← 0 …+ (suc (suc n)) $ (suc (suc n) ∸ k) choose k ]
            ≡⟨ {!!} ⟩
          fib n + fib (suc n)
        ∎
        where
          open P.≡-Reasoning
