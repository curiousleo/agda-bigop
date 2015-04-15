module Proofs where

  open import Bigop.Lemmas

  open import Algebra

  open import Function

  open import Data.Unit hiding (setoid)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.EqReasoning as EqR

  module GaussSquared where

    open import Data.List
    open import Data.Empty
    open import Relation.Nullary.Decidable

    open import Data.Nat using (suc)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    open SemiringWithoutOneLemmas semiringWithoutOne
    open CommutativeMonoidLemmas +-commutativeMonoid
    open MonoidLemmas +-monoid

    open Fold +-monoid using (fold; Σ-syntax)
    open EqR setoid

    open RangeLemmas

    lemma : ∀ n → ¬ (Odd (n + n))
    lemma n = {!!}

    open import Relation.Unary

    Σ-last-yes : ∀ {ℓ} {i} {I : Set i} (f : I → ℕ) (xs : List I) (x : I) →
                 {P : Pred I ℓ} (p : Decidable P) → True (p x) →
                 Σ[ k ← (xs ∷ʳ x) ∥ p $ f k ] ≈ Σ[ k ← xs ∥ p $ f k ] + f x
    Σ-last-yes f xs x p tpx = begin
      Σ[ k ← (xs ∷ʳ x) ∥ p $ f k ]  ≈⟨ P.cong (fold f) (last-yes xs x p tpx) ⟩
      Σ[ k ← (xs ∥ p) ∷ʳ x $ f k ]  ≈⟨ Σ-last f x (xs ∥ p) ⟩
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
        ≈⟨ Σ-last-yes id (0 … (n + n)) (n + (suc n)) odd (fromWitness (2n+1-odd n)) ⟩
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

            ⓑ = last-no {P = Odd} (0 … _+_ n (suc n)) (_+_ (suc n) (suc n)) odd (fromWitness ¬last-odd)

  module GaussFormula where

    open import Data.Nat using (suc)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    open SemiringWithoutOneLemmas semiringWithoutOne
    open CommutativeMonoidLemmas +-commutativeMonoid
    open MonoidLemmas +-monoid

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
        open import Data.List

        open RangeLemmas

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
          Σ[ x ← 0 … n ∷ʳ suc n $ x ]  ≡⟨ Σ-last id (suc n) (0 … n) ⟩
          Σ[ x ← 0 … n $ x ] + suc n   ∎

  open import Matrix hiding (lookup; tabulate)

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

    open Fold +-monoid using (Σ-syntax)

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

    open Fold +-monoid using (fold; Σ-syntax)

    infixr 8 _^_

    _^_ : ℕ → ℕ → ℕ
    x ^ 0 = 1
    x ^ (suc n) = x * x ^ n

    _choose_ : ℕ → ℕ → ℕ
    _     choose 0     = 1
    0     choose suc k = 0
    suc n choose suc k = n choose k + n choose (suc k)

    choose-lemma : ∀ m n → n choose ((suc m) + n) ≡ 0
    choose-lemma m 0 = P.refl
    choose-lemma m (suc n) = ➀ ⟨ +-cong ⟩ ➁
      where
        open P.≡-Reasoning
        
        ➀ : n choose (m + suc n) ≡ 0
        ➀ = begin
          n choose (m + suc n)
            ≡⟨ P.refl ⟨ P.cong₂ _choose_ ⟩ begin
               m + suc n
                 ≡⟨ +-comm m (suc n) ⟩
               suc (n + m)
                 ≡⟨ P.cong suc (+-comm n m) ⟩
               suc (m + n) ∎
            ⟩
          n choose suc (m + n)
            ≡⟨ choose-lemma m n ⟩
          0 ∎

        ➁ : n choose suc (m + suc n) ≡ 0
        ➁ = begin
          n choose suc (m + suc n)
            ≡⟨ (P.refl {x = n}) ⟨ P.cong₂ _choose_ ⟩ begin
               suc (m + suc n)
                 ≡⟨ P.cong suc (+-comm m (suc n)) ⟩
               suc (suc (n + m))
                 ≡⟨ P.cong (suc ∘ suc) (+-comm n m) ⟩
               suc (suc m + n) ∎
            ⟩
          n choose suc (suc m + n)
            ≡⟨ choose-lemma (suc m) n ⟩
          0 ∎

    _! : ℕ → ℕ
    0 !     = 1
    suc n ! = suc n * (n !)

    fib : ℕ → ℕ
    fib 0             = 0
    fib 1             = 1
    fib (suc (suc n)) = fib n + fib (suc n)

    module BinomialTheorem where

      open import Data.Product using (proj₁; proj₂)

      open EqR setoid
      open import Level renaming (zero to lzero; suc to lsuc)
      open RangeLemmas {I = ℕ} {ℓ = lzero}

      proof : ∀ x n → Σ[ k ← 0 … n $ n choose k * x ^ k ] ≈ (suc x) ^ n
      proof x 0       = refl
      proof x (suc n) = begin
        1 + Σ[ k ← 1 … suc n $ (suc n) choose k * x ^ k ]
          ≈⟨ refl {x = 1} ⟨ +-cong ⟩ begin
            Σ[ k ← 1 … suc n $ (suc n) choose k * x ^ k ]
              ≈⟨ sym $ Σ-cong {g = f (suc n)} suc (λ _ → refl) (0 … n)
                       ⟨ trans ⟩ P.cong (fold (f (suc n))) (suc-lemma 0 (suc n)) ⟩
            Σ[ k ← 0 … n $ (suc n) choose (suc k) * x ^ (suc k) ]
              ≈⟨ Σ-cong′ {f = λ k → f (suc n) (suc k)} (λ _ → refl) (0 … n) ⟩
            Σ[ k ← 0 … n $ (n choose k + n choose (suc k)) * x ^ (suc k) ]
              ≈⟨ Σ-cong′ {f = λ k → (n choose k + n choose (suc k)) * x ^ (suc k)}
                         (λ k → distribʳ (x ^ (suc k)) (n choose k) _) (0 … n) ⟩
            Σ[ k ← 0 … n $ n choose k * x ^ (suc k)
                                  + n choose (suc k) * x ^ (suc k) ]
              ≈⟨ sym $ Σ-lift {J = ℕ}
                              (λ k → n choose k * x ^ (suc k)) (λ k → f n (suc k))
                              (0 … n) ⟩
            Σ[ k ← 0 … n $ n choose k * x ^ (suc k) ]
            + Σ[ k ← 0 … n $ n choose (suc k) * x ^ (suc k) ] ∎
          ⟩
        1 + (Σ[ k ← 0 … n $ n choose k * x ^ (suc k) ]
             + Σ[ k ← 0 … n $ n choose (suc k) * x ^ (suc k) ])
          ≈⟨ +-reorder 1 Σ[ k ← 0 … n $ n choose k * x ^ (suc k) ] _ ⟩
        Σ[ k ← 0 … n $ n choose k * x ^ (suc k) ]
        + (1 + Σ[ k ← 0 … n $ n choose (suc k) * x ^ (suc k) ])
          ≈⟨ ➀ ⟨ +-cong ⟩ ➁ ⟩
          x * Σ[ k ← 0 … n $ n choose k * x ^ k ]
        +     Σ[ k ← 0 … n $ n choose k * x ^ k ]
          ≈⟨ +-cong (refl {x = x * _})
                    (sym $ proj₁ *-identity Σ[ k ← 0 … n $ f n k ]) ⟩
          x * Σ[ k ← 0 … n $ n choose k * x ^ k ]
        + 1 * Σ[ k ← 0 … n $ n choose k * x ^ k ]
          ≈⟨ sym $ distribʳ _ x 1 ⟩
        (x + 1) * Σ[ k ← 0 … n $ n choose k * x ^ k ]
          ≈⟨ *-cong (+-comm x 1) (proof x n) ⟩
        (1 + x) * (1 + x) ^ n ∎

        where

          f : ℕ → ℕ → ℕ
          f n k = n choose k * x ^ k

          +-reorder : ∀ x y z → x + (y + z) ≈ y + (x + z)
          +-reorder x y z = begin
            x + (y + z)  ≈⟨ sym $ +-assoc x y z ⟩
            (x + y) + z  ≈⟨ +-cong (+-comm x y) refl ⟩
            (y + x) + z  ≈⟨ +-assoc y x z ⟩
            y + (x + z)  ∎

          ➀ : Σ[ k ← 0 … n $ n choose k * x ^ (suc k) ] ≈ x * Σ[ k ← 0 … n $ n choose k * x ^ k ]
          ➀ = begin
            Σ[ k ← 0 … n $ n choose k * x ^ (suc k) ]  ≈⟨ Σ-cong′ reorder (0 … n) ⟩
            Σ[ k ← 0 … n $ x * (n choose k * x ^ k) ]  ≈⟨ sym $ Σ-distrˡ (f n) x (0 … n) ⟩
            x * Σ[ k ← 0 … n $ n choose k * x ^ k ]    ∎

            where

              reorder : ∀ k → n choose k * x ^ (suc k) ≈ x * (n choose k * x ^ k)
              reorder k = begin
                n choose k * (x * x ^ k)  ≈⟨ sym $ *-assoc (n choose k) _ _ ⟩
                (n choose k * x) * x ^ k  ≈⟨ *-comm (n choose k) _ ⟨ *-cong ⟩ refl ⟩
                (x * n choose k) * x ^ k  ≈⟨ *-assoc x _ _ ⟩
                x * (n choose k * x ^ k)  ∎

          open import Data.List

          ➁ : 1 + Σ[ k ← 0 … n $ n choose (suc k) * x ^ (suc k) ]
              ≈ Σ[ k ← 0 … n $ n choose k * x ^ k ]
          ➁ = begin
            1 + Σ[ k ← 0 … n $ n choose (suc k) * x ^ (suc k) ]
              ≈⟨ (refl {x = 1}) ⟨ +-cong ⟩ begin
                Σ[ k ← 0 … n $ n choose (suc k) * x ^ (suc k) ]
                  ≈⟨ Σ-cong {g = f n} suc (λ k → refl) (0 … n) ⟩
                Σ[ k ← map suc (0 … n) $ n choose k * x ^ k ]
                  ≈⟨ P.cong (fold $ f n) (suc-lemma 0 (suc n)) ⟩
                Σ[ k ← 1 … suc n $ n choose k * x ^ k ]
                  ≈⟨ P.cong (fold $ f n) (suc-last-lemma 1 n) ⟩
                Σ[ k ← (1 … n) ∷ʳ (suc n) $ n choose k * x ^ k ]
                  ≈⟨ Σ-last (f n) (suc n) (1 … n) ⟩
                Σ[ k ← 1 … n $ n choose k * x ^ k ] + n choose (suc n) * x ^ (suc n)
                  ≈⟨ +-cong (refl {x = Σ[ k ← 1 … n $ f n k ]})
                            (choose-lemma 0 n ⟨ *-cong ⟩ refl ⟨ trans ⟩ zeroˡ n) ⟩
                Σ[ k ← 1 … n $ n choose k * x ^ k ] + 0
                  ≈⟨ proj₂ +-identity _ ⟩
                Σ[ k ← 1 … n $ n choose k * x ^ k ] ∎
              ⟩
            1 + Σ[ k ← 1 … n $ n choose k * x ^ k ]
              ≈⟨ refl ⟩
            Σ[ k ← 0 ∷ (1 … n) $ n choose k * x ^ k ]
              ≈⟨ P.cong (fold $ f n) (suc-head-lemma 0 n) ⟩
            Σ[ k ← 0 … n $ n choose k * x ^ k ] ∎

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
