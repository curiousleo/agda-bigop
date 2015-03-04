module Prototypes.SimpleProofs where

  open import Prototypes.BigopBijection

  open import Function using (id)
  
  open import Data.Nat
  open import Data.Nat.Properties.Simple
  open import Data.Fin hiding (_+_)
  open import Data.Unit.Base

  open import Function using (_∘_)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary.Decidable hiding (map)


  distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
  distribˡ-*-+ m n o
    rewrite
      *-comm m n
    | *-comm m o
    | sym (distribʳ-*-+ m n o)
    | *-comm (n + o) m = refl

  module GaussFormula where

    expr : ℕ → ℕ
    expr n = (Sum n) ⟦ toℕ ⟧

    proof : (n : ℕ) → 2 * expr (1 + n) ≡ n * (1 + n)
    proof zero = refl
    proof (suc n) =
      begin
        2 * expr (2 + n)               ≡⟨ cong (_*_ 2) lemma ⟩
        2 * ((1 + n) + expr (1 + n))   ≡⟨ distribˡ-*-+ 2 (1 + n) (expr (1 + n)) ⟩
        2 * (1 + n) + 2 * expr (1 + n) ≡⟨ cong (_+_ (2 * (1 + n))) (proof n) ⟩
        2 * (1 + n) + n * (1 + n)      ≡⟨ sym (distribʳ-*-+ (1 + n) 2 n) ⟩
        (2 + n) * (1 + n)              ≡⟨ *-comm (2 + n) (1 + n) ⟩
        (1 + n) * (2 + n)
      ∎
      where
        open ≡-Reasoning
        open import Data.Vec

        open import Data.Vec.Properties

        -- TODO: express this in terms of `Sum-lemma`

        lemma : ∀ {m} → expr (suc m) ≡ m + expr m
        lemma {zero} = refl
        lemma {suc m}
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
              | sym (+-assoc (f 0) m (sum (tabulate {m} (f ∘ sucℕ ∘ toℕ))))
              | +-comm (f 0) m
              | sym (+-assoc m (f 0) (sum (tabulate {m} (f ∘ sucℕ ∘ toℕ))))
              = refl

  open import Prototypes.Matrix

  module MatrixAssoc {p q r s}
         (A : Matrix ℕ p q) (B : Matrix ℕ q r) (C : Matrix ℕ r s) where

--  syntax innerSum ⟦ (λ x → e) ⟧ = Σ x 〖 e 〗 -- or ⨁

    open import Data.Vec
    open import Data.Vec.Properties

    A×〈B×C〉 : Fin p → Fin s → ℕ
    A×〈B×C〉 = λ i j → (Sum q)
      ⟦ (λ k → A [ i , k ] * ((Sum r)
        ⟦ (λ l → B [ k , l ] * C [ l , j ]) ⟧)) ⟧
{-
    = λ i j → Σ k 〖 A [ i , k ] * Σ l 〖 B [ k , l ] * C [ l , j ] 〗 〗
-}

    〈A×B〉×C : Fin p → Fin s → ℕ
    〈A×B〉×C = λ i j → (Sum r)
      ⟦ (λ l → ((Sum q)
        ⟦ (λ k → A [ i , k ] * B [ k , l ]) ⟧)
        * C [ l , j ]) ⟧
{-
    = λ i j → Σ l 〖 Σ k 〖 A [ i , k ] * B [ k , l ] 〗 * C [ l , j ] 〗
-}
    eq : ∀ {i j} → A×〈B×C〉 i j ≡ 〈A×B〉×C i j
    eq {i} {j} =
      begin
        A×〈B×C〉 i j
          ≡⟨ refl ⟩
        (Sum q) ⟦ (λ k → A [ i , k ] * ((Sum r) ⟦ (λ l → B [ k , l ] * C [ l , j ]) ⟧)) ⟧
          ≡⟨ refl ⟩
        sum (map (λ k → A [ i , k ] * sum (map (λ l → B [ k , l ] * C [ l , j ])
                                               (allFin r)))
                 (allFin q))
          ≡⟨ {!!} ⟩
        sum (map (λ k → sum (map (λ l → A [ i , k ] * (B [ k , l ] * C [ l , j ]))
                                 (allFin r)))
                 (allFin q))
          ≡⟨ refl ⟩
        (Sum q) ⟦ (λ k → ((Sum r) ⟦ (λ l → A [ i , k ] * (B [ k , l ] * C [ l , j ])) ⟧)) ⟧
          ≡⟨ {!!} ⟩
        sum (map (λ l → sum (map (λ k → A [ i , k ] * (B [ k , l ] * C [ l , j ]))
                                 (allFin q)))
                 (allFin r))
          ≡⟨ refl ⟩
        (Sum r) ⟦ (λ l → ((Sum q) ⟦ (λ k → A [ i , k ] * (B [ k , l ] * C [ l , j ])) ⟧)) ⟧
          ≡⟨ {!!} ⟩
        sum (map (λ l → sum (map (λ k → (A [ i , k ] * B [ k , l ]) * C [ l , j ])
                                 (allFin q)))
                 (allFin r))
          ≡⟨ refl ⟩
        (Sum r) ⟦ (λ l → ((Sum q) ⟦ (λ k → (A [ i , k ] * B [ k , l ]) * C [ l , j ]) ⟧)) ⟧
          ≡⟨ {!!} ⟩
        sum (map (λ l → sum (map (λ k → A [ i , k ] * B [ k , l ])
                                 (allFin q))
                        * C [ l , j ])
                 (allFin r))
          ≡⟨ refl ⟩
        (Sum r) ⟦ (λ l → ((Sum q) ⟦ (λ k → (A [ i , k ] * B [ k , l ])) ⟧ * C [ l , j ])) ⟧
          ≡⟨ refl ⟩
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
