open import Dijkstra.Algebra

module Dijkstra.Correctness
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Dijkstra.Algebra.Properties
open import Dijkstra.Algorithm alg renaming (module UsingAdj to Algorithm-UsingAdj)
open import Dijkstra.Adjacency alg
-- open import Dijkstra.Properties alg renaming (module UsingAdj to Properties-UsingAdj)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_; to-from; inject₁-lemma; bounded)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Matrix
open import Data.Nat
  using (ℕ; zero; suc; z≤n; s≤s)
  renaming (_+_ to _N+_; _≤_ to _N≤_; decTotalOrder to ℕ-decTotalOrder)
open import Data.Nat.MoreProperties
open import Data.Nat.Properties using (≤-step)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)

open import Function using (_$_; _∘_; flip)

open DecTotalOrder ℕ-decTotalOrder using () renaming (refl to ≤-refl)
open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Bigop.SubsetCore +-commutativeMonoid
open EqR setoid

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open Algorithm-UsingAdj {n} i adj
--  open Properties-UsingAdj {n} i adj

  pRLS : (ctd : ℕ) {lt : ctd N≤ n} → Pred (Fin (suc n)) _
  pRLS ctd {lt} j = let r = estimate ctd {lt} in
    r j ≈ I[ i , j ] + (⨁[ k ← visited ctd {lt} ] (r j + r k * A[ k , j ]))
    -- I[ i , j ] + ⨁[ k ← visited ctd ] (r k * A[ k , j ]) ≤ r j

  visited-nonempty : (ctd : ℕ) {lt : ctd N≤ n} → Nonempty (visited ctd {lt})
  visited-nonempty zero      = Sub.⁅i⁆-nonempty i
  visited-nonempty (suc ctd) = Sub.∪-nonempty¹ _ _ (visited-nonempty ctd)

  q-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → j ∈ visited ctd {≤-step′ lt} →
            let q = Sorted.head _ (queue ctd {lt})
                r = estimate ctd {≤-step′ lt}
            in r j + r q ≈ r j
  q-lemma ctd {lt} j j∈vs = {!!}

  estimate-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → j ∈ visited ctd {≤-step′ lt} →
                   estimate (suc ctd) {lt} j ≈ estimate ctd {≤-step′ lt} j
  estimate-lemma ctd {lt} j j∈vs =
    begin
      r j +  r q * A[ q , j ]          ≈⟨ +-cong (sym (q-lemma ctd {lt} j j∈vs)) refl ⟩
     (r j +  r q) + r q * A[ q , j ]   ≈⟨ +-assoc _ _ _ ⟩
      r j + (r q  + r q * A[ q , j ])  ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
      r j +  r q                       ≈⟨ q-lemma ctd {lt} j j∈vs ⟩
      r j
    ∎
    where
      r = estimate ctd {≤-step′ lt}
      q  = Sorted.head _ (queue ctd {lt})
      vs = visited ctd {≤-step′ lt}

  pcorrect : (ctd : ℕ) {lt : ctd N≤ n} → ∀ j → pRLS ctd {lt} j
  pcorrect zero      {lt} j with i ≟ j
  ... | yes i≡j =
    begin
      r j             ≡⟨⟩
      A[ i , j ]      ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) j≡i ⟩
      A[ i , i ]      ≡⟨ Adj.diag adj i ⟩
      1#              ≈⟨ sym (proj₁ +-zero _) ⟩
      1#         + _  ≡⟨ P.cong₂ _+_ (P.sym (Adj.diag I j)) P.refl ⟩
      I[ j , j ] + _  ≡⟨ P.cong₂ _+_ (P.cong₂ I[_,_] j≡i (P.refl {x = j})) P.refl ⟩
      I[ i , j ] + _
    ∎
    where
      r = estimate zero {z≤n}
      j≡i = P.sym i≡j

  ... | no ¬i≡j =
    begin
      A[ i , j ]                       ≈⟨ sym (proj₁ +-identity _) ⟩
      0#                 + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl ⟩
      diagonal 0# 1# i j + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl ⟩
      I[ i , j ]         + A[ i , j ]  ≈⟨ +-cong refl (sym (+-idempotent _)) ⟩
      I[ i , j ]         + (r j + A[ i , j ]) ≈⟨ +-cong refl (+-cong refl (sym (*-identityˡ _))) ⟩
      I[ i , j ]         + (r j + 1# * A[ i , j ]) ≡⟨ P.cong₂ _+_ P.refl (P.cong₂ _+_ P.refl (P.cong₂ _*_ (P.sym (Adj.diag adj i)) P.refl)) ⟩
      I[ i , j ]         + (r j + r i * A[ i , j ]) ≈⟨ +-cong refl (sym (fold-⁅i⁆ (λ k → r j + r k * A[ k , j ]) i)) ⟩
      I[ i , j ]         + (⨁[ k ← ⁅ i ⁆ ] (r j + r k * A[ k , j ]))
    ∎
    where
      r = estimate zero {z≤n}

  pcorrect (suc ctd) {lt} j =
    begin
      r′ j
        ≡⟨⟩
      r j + r q * A[ q , j ]
        ≈⟨ +-cong (pcorrect ctd {≤-step′ lt} j) (sym (+-idempotent _)) ⟩
      (I[ i , j ] + (⨁[ k ← vs ] (r j + r k * A[ k , j ]))) + (r q * A[ q , j ] + r q * A[ q , j ])
        ≈⟨ +-assoc _ _ _ ⟩
      I[ i , j ] + ((⨁[ k ← vs ] (r j + r k * A[ k , j ])) + (r q * A[ q , j ] + r q * A[ q , j ]))
        ≈⟨ +-cong refl (+-cong (fold-distr′ +-idempotent f (r j) (vs) (visited-nonempty ctd)) refl) ⟩
      I[ i , j ] + ((r j + (⨁[ k ← vs ] (r k * A[ k , j ]))) + (r q * A[ q , j ] + r q * A[ q , j ]))
        ≈⟨ +-cong refl (+-cong (+-comm _ _) refl) ⟩
      I[ i , j ] + (((⨁[ k ← vs ] (r k * A[ k , j ])) + r j) + (r q * A[ q , j ] + r q * A[ q , j ]))
        ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
      I[ i , j ] + ((⨁[ k ← vs ] (r k * A[ k , j ])) + (r j + (r q * A[ q , j ] + r q * A[ q , j ])))
        ≈⟨ +-cong refl (+-cong refl (sym (+-assoc _ _ _))) ⟩
      I[ i , j ] + ((⨁[ k ← vs ] (r k * A[ k , j ])) + ((r j + r q * A[ q , j ]) + r q * A[ q , j ]))
        ≡⟨⟩
      I[ i , j ] + ((⨁[ k ← vs ] (r k * A[ k , j ])) + (r′ j + r q * A[ q , j ]))
        ≈⟨ +-cong refl (sym (+-assoc _ _ _)) ⟩
      I[ i , j ] + (((⨁[ k ← vs ] (r k * A[ k , j ])) + r′ j) + r q * A[ q , j ])
        ≈⟨ +-cong refl (+-cong (+-cong (fold-cong f f′ vs (λ k k∈vs → lemma k k∈vs)) refl) (*-cong (sym (+-absorbs-* _ _)) refl)) ⟩
      I[ i , j ] + (((⨁[ k ← vs ] (r′ k * A[ k , j ])) + r′ j) + r′ q * A[ q , j ])
        ≈⟨ +-cong refl (+-cong (+-comm _ _) (sym (fold-⁅i⁆ f′ q))) ⟩
      I[ i , j ] + ((r′ j + (⨁[ k ← vs ] (r′ k * A[ k , j ]))) + (⨁[ k ← ⁅ q ⁆ ] (r′ k * A[ k , j ])))
        ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
      I[ i , j ] + (r′ j + ((⨁[ k ← vs ] (r′ k * A[ k , j ])) + (⨁[ k ← ⁅ q ⁆ ] (r′ k * A[ k , j ]))))
        ≈⟨ +-cong refl (+-cong refl (sym (fold-∪ +-idempotent f′ (visited ctd) ⁅ q ⁆))) ⟩
      I[ i , j ] + (r′ j + (⨁[ k ← vs ∪ ⁅ q ⁆ ] (r′ k * A[ k , j ])))
        ≈⟨ +-cong refl (sym (fold-distr′ +-idempotent f′ (r′ j) (visited ctd ∪ ⁅ q ⁆) (visited-nonempty (suc ctd)))) ⟩
      I[ i , j ] + (⨁[ k ← vs ∪ ⁅ q ⁆ ] (r′ j + r′ k * A[ k , j ]))
        ≡⟨⟩
      I[ i , j ] + (⨁[ k ← visited (suc ctd) {lt} ] (r′ j + r′ k * A[ k , j ]))
    ∎
    where
      r′ = estimate (suc ctd) {lt}
      r  = estimate ctd {≤-step′ lt}
      q  = Sorted.head _ (queue ctd {lt})
      f  = λ k → r k * A[ k , j ]
      f′ = λ k → r′ k * A[ k , j ]
      vs = visited ctd {≤-step′ lt}
      lemma : ∀ k → k ∈ vs → f k ≈ f′ k
      lemma k k∈vs = {!!}


  RLS : (ctd : ℕ) {lt : ctd N≤ n} → Pred (Fin (suc n)) _
  RLS ctd {lt} j = let r = estimate ctd {lt} in
    r j ≈ I[ i , j ] + (⨁[ k ← ⊤ ] (r j + r k * A[ k , j ]))

  correct : ∀ j → RLS n {≤-refl} j
  correct j = pRLS→RLS (pcorrect n j)
    where
      pRLS→RLS : ∀ {j} → pRLS n {≤-refl} j → RLS n {≤-refl} j
      pRLS→RLS {j} p =
        begin
          r j
            ≈⟨ p ⟩
          I[ i , j ] + (⨁[ k ← visited n {≤-refl} ] (r j + r k * A[ k , j ]))
            ≡⟨ P.cong₂ _+_ P.refl (P.cong₂ ⨁-syntax P.refl (Sub.n→⊤ (visited n) (visited-lemma n))) ⟩
          I[ i , j ] + (⨁[ k ← ⊤ ] (r j + r k * A[ k , j ]))
        ∎
        where
          r = estimate n {≤-refl}
