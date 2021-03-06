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
        open Bigop (Sum (1 + n))
        open BigopLemmas (Sum (1 + n))

        lemma : fold· (Sum (2 + n)) toℕ ≡ (1 + n) + fold· (Sum (1 + n)) toℕ
        lemma = {!!} -- foldr·-map-lemmaʳ ε (enum index) toℕ

  open import Prototypes.Matrix hiding (lookup; tabulate)

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
          ≡⟨ {!sym distr!} ⟩
        sum (map (λ k → sum (map (_*_ (A [ i , k ])) (map (λ l → B [ k , l ] * C [ l , j ])
                                                          (allFin r))))
                 (allFin q))
          ≡⟨ {!map-∘!} ⟩
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
          ≡⟨ {!*-assoc!} ⟩
        sum (map (λ l → sum (map (λ k → (A [ i , k ] * B [ k , l ]) * C [ l , j ])
                                 (allFin q)))
                 (allFin r))
          ≡⟨ refl ⟩
        (Sum r) ⟦ (λ l → ((Sum q) ⟦ (λ k → (A [ i , k ] * B [ k , l ]) * C [ l , j ]) ⟧)) ⟧
          ≡⟨ {!!} ⟩
        sum (map (λ l → sum (map (λ k → C [ l , j ] * (A [ i , k ] * B [ k , l ]))
                                 (allFin q)))
                 (allFin r))
          ≡⟨ {!!} ⟩
        sum (map (λ l → sum (map (_*_ (C [ l , j ])) (map (λ k → C [ l , j ] * (A [ i , k ] * B [ k , l ]))
                                                          (allFin q))))
                 (allFin r))
          ≡⟨ {!distr!} ⟩
        sum (map (λ l → C [ l , j ] * sum (map (λ k → C [ l , j ] * (A [ i , k ] * B [ k , l ]))
                                               (allFin q)))
                 (allFin r))
          ≡⟨ {!*-comm!} ⟩
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

        distr : ∀ {n k} (v : Vec ℕ n) →
                sum (map (_*_ k) v) ≡ k * (sum v)
        distr {zero}  {k} [] = *-comm 0 k
        distr {suc n} {k} (x ∷ v)
          rewrite
            distr {n} {k} v = sym (distribˡ-*-+ k x (sum v))

        lemma₁ : ∀ k → sum (map (_*_ (A [ i , k ])) (map (λ l → B [ k , l ] * C [ l , j ])
                                                          (allFin r))) ≡
                 sum (map (λ l → A [ i , k ] * (B [ k , l ] * C [ l , j ]))
                                 (allFin r))
        lemma₁ k
          rewrite
            distr (map (λ l → B [ k , l ] * C [ l , j ]) (allFin r))
            = {!refl!}

{-
        lemma₀ : sum (map (λ k → A [ i , k ] *
                              sum (map (λ l → B [ k , l ] * C [ l , j ])
                                       (tabulate id)))
                          (tabulate id)) ≡
                 sum (map (λ k → sum (map (λ l → A [ i , k ] *
                                             (B [ k , l ] * C [ l , j ]))
                                          (tabulate id)))
                          (tabulate id))
-}
        lem₂ : ∀ {x n} {y} {f : Fin n → ℕ} → x * f y ≡ ((_*_ x) ∘ f) y
        lem₂ = refl


        lem₁ : ∀ {x n} {f : Fin n → ℕ} →
               map (λ y → x * f y) (tabulate id) ≡
               map (_*_ x) (map f (tabulate id))
        lem₁ {x} {n} {f} =
          begin
            map (λ y → x * f y) (tabulate id)                    ≡⟨ refl ⟩
            replicate (λ y → x * f y) ⊛ tabulate id              ≡⟨ {! map (_*_ x) (map f (tabulate id))!} ⟩
            replicate (_*_ x) ⊛ (replicate f ⊛ tabulate id)      ≡⟨ refl ⟩
            map (_*_ x) (map f (tabulate id))
          ∎
{-
        lemma₀ : ∀ {x n} (f : Fin n → ℕ) →
                 x * sum (map f (allFin n)) ≡
                 sum (map (λ y → x * f y) (allFin n))
        lemma₀ {k}
          rewrite
            refl
      --    | distr {k = A [ i , k ]} (map (λ l → B [ k , l ] * C [ l , j ])
      --                                   (tabulate id))
            = {!!} -- distr {k = A [ i , k ]} (map (λ l → B [ k , l ] * C [ l , j ]) (tabulate id))
-}
