open import Dijkstra.Algebra

module Dijkstra.Properties
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Dijkstra.Algebra.Properties
open import Dijkstra.Algorithm alg renaming (module UsingAdj to Algorithm-UsingAdj)
open import Dijkstra.Adjacency alg

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_; to-from; inject₁-lemma; bounded)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Matrix
open import Data.Nat
  using (ℕ; zero; suc; z≤n; s≤s)
  renaming (_+_ to _N+_; _≤_ to _N≤_)
open import Data.Nat.MoreProperties
open import Data.Nat.Properties using (≤-step)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Product using (proj₁; proj₂; _,_; ∃; ∃₂)
open import Data.Sum
import Data.Vec as V
import Data.Vec.Properties as VP
import Data.Vec.Sorted as Sorted

open import Function.Equivalence using (module Equivalence)
open import Function.Equality using (module Π)
open Π using (_⟨$⟩_)

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)
open P.≡-Reasoning
  using ()
  renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _■)

open import Function using (_$_; _∘_; flip)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
-- open import Bigop.SubsetCore +-commutativeMonoid
open EqR setoid

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open Algorithm-UsingAdj i adj

  q-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ k → k ∉ visited ctd {≤-step′ lt} →
            let r = estimate ctd {≤-step′ lt}
                q = Sorted.head _ (queue ctd {lt}) in
            r k + r q ≈ r q
  q-lemma ctd {lt} k k∉vs = rq⊴ᴸrk⟶rk+rq≈rq ⟨$⟩ ≤-lemma (S.head-≤ (∈-lemma k∉vs))
    where
      r = estimate ctd {≤-step′ lt}

      module S = Sorted (estimateOrder (V.tabulate r))
      open DecTotalOrder (estimateOrder (V.tabulate r))
        using () renaming (_≤_ to _≤ᵉ_)

      q = S.head (queue ctd {lt})

      ∈-lemma : ∀ {k} → k ∉ visited ctd {≤-step′ lt} → k S.∈ queue ctd {lt}
      ∈-lemma {k} k∉vs = q′→q ctd {lt} (λ qs → k S.∈ qs) (∈-lemma′ k∉vs)
        where
          ∈-lemma′ : ∀ {k} → k ∉ visited ctd {≤-step′ lt} → k S.∈ queue′ ctd {≤-step′ lt}
          ∈-lemma′ k∉vs = S.fromVec-∈¹ (Sub.toVec-∈¹ (Sub.∁-∈′ k∉vs))

      ≤-lemma : ∀ {a b} → a ≤ᵉ b → r a ≤ r b
      ≤-lemma {a} {b} (x , eq) = x ,
        (begin
          r a                            ≡⟨ P.sym (VP.lookup∘tabulate r a) ⟩
          V.lookup a (V.tabulate r)      ≈⟨ eq ⟩
          V.lookup b (V.tabulate r) + x  ≡⟨ P.cong₂ _+_ (VP.lookup∘tabulate r b) P.refl ⟩
          r b + x
        ∎)

      open Equivalence (equivalentᴸ (r q) (r k)) renaming (from to rq⊴ᴸrk⟶rk+rq≈rq)

  not-visited : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ k → k ∉ visited (suc ctd) {lt} →
                k ∉ visited ctd {≤-step′ lt}
  not-visited ctd {lt} k k∉vs′ k∈vs = k∉vs′ (Sub.∪-∈′ k _ _ k∈vs)

  pcorrect-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j k →
            let vs = visited ctd {≤-step′ lt}
                r = estimate ctd {≤-step′ lt} in
            j ∈ vs → k ∉ vs → r j + r k ≈ r j
  pcorrect-lemma zero j k j∈vs k∉vs =
    begin
      A[ i , j ] + _  ≡⟨ P.cong₂ _+_ lemma P.refl ⟩
      1#         + _  ≈⟨ proj₁ +-zero _ ⟩
      1#              ≡⟨ P.sym lemma ⟩
      A[ i , j ]
    ∎
    where
      lemma : A[ i , j ] ≡ 1#
      lemma =
        start
          A[ i , j ]  ≣⟨ P.cong₂ A[_,_] (P.refl {x = i}) (Sub.i∈⁅i⁆′ i j j∈vs) ⟩
          A[ i , i ]  ≣⟨ Adj.diag adj i ⟩
          1#
        ■

  pcorrect-lemma (suc ctd) {lt} j k j∈vs′ k∉vs′ with Sub.∪-∈ {suc n} j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈vs′

  ... | inj₁ j∈vs =
    begin
      r′ j + r′ k
        ≡⟨⟩
      (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])
        ≈⟨ +-cong (+-comm _ _) refl ⟩
      (r q * A[ q , j ] + r j) + (r k + r q * A[ q , k ])
        ≈⟨ +-assoc _ _ _ ⟩
      r q * A[ q , j ] + (r j + (r k + r q * A[ q , k ]))
        ≈⟨ +-cong refl (sym (+-assoc _ _ _)) ⟩
      r q * A[ q , j ] + ((r j + r k) + r q * A[ q , k ])
        ≈⟨ +-cong refl (+-cong (pcorrect-lemma ctd {≤-step′ lt} j k j∈vs (not-visited ctd k k∉vs′)) refl) ⟩
      r q * A[ q , j ] + (r j + r q * A[ q , k ])
        ≈⟨ +-cong refl (+-cong (sym (pcorrect-lemma ctd {≤-step′ lt} j q j∈vs (head∉visited ctd))) refl) ⟩
      r q * A[ q , j ] + ((r j + r q) + r q * A[ q , k ])
        ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
      r q * A[ q , j ] + (r j + (r q + r q * A[ q , k ]))
        ≈⟨ +-cong refl (+-cong refl (+-absorbs-* _ _)) ⟩
      r q * A[ q , j ] + (r j + r q)
        ≈⟨ +-cong refl (pcorrect-lemma ctd {≤-step′ lt} j q j∈vs (head∉visited ctd)) ⟩
      r q * A[ q , j ] + r j
        ≈⟨ +-comm _ _ ⟩
      r j + r q * A[ q , j ]
        ≡⟨⟩
      r′ j
    ∎
    where
      r  = estimate ctd {≤-step′ (≤-step′ lt)}
      r′ = estimate (suc ctd) {≤-step′ lt}
      q  = Sorted.head _ (queue ctd {≤-step′ lt})

  ... | inj₂ j∈⁅q⁆ =
    begin
      r′ j + r′ k
        ≡⟨⟩
      (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])
        ≡⟨ P.cong₂ _+_ (P.cong₂ _+_ (P.cong r j≡q) P.refl) P.refl ⟩
      (r q + r q * A[ q , j ]) + (r k + r q * A[ q , k ])
        ≈⟨ +-cong (+-absorbs-* _ _) refl ⟩
      r q + (r k + r q * A[ q , k ])
        ≈⟨ sym (+-assoc _ _ _) ⟩
      (r q + r k) + r q * A[ q , k ]
        ≈⟨ +-cong (+-comm _ _) refl ⟩
      (r k + r q) + r q * A[ q , k ]
        ≈⟨ +-assoc _ _ _ ⟩
      r k + (r q + r q * A[ q , k ])
        ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
      r k + r q
        ≈⟨ q-lemma ctd {≤-step′ lt} k (not-visited ctd k k∉vs′) ⟩
      r q
        ≈⟨ sym (+-absorbs-* _ _) ⟩
      r q + r q * A[ q , j ]
        ≡⟨ P.cong₂ _+_ (P.cong r (P.sym j≡q)) P.refl ⟩
      r j + r q * A[ q , j ]
        ≡⟨⟩
      r′ j
    ∎
    where
      r  = estimate ctd {≤-step′ (≤-step′ lt)}
      r′ = estimate (suc ctd) {≤-step′ lt}
      q  = Sorted.head _ (queue ctd {≤-step′ lt})
      j≡q : j ≡ q
      j≡q = Sub.i∈⁅i⁆′ {suc n} q j j∈⁅q⁆

  estimate-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ k → k ∈ visited ctd {≤-step′ lt} →
                   estimate (suc ctd) {lt} k ≈ estimate ctd {≤-step′ lt} k
  estimate-lemma ctd {lt} k k∈vs =
    begin
      r′ k
        ≡⟨⟩
      r k + r q * A[ q , k ]
        ≈⟨ +-cong (sym (pcorrect-lemma ctd {lt} k q k∈vs (head∉visited ctd))) refl ⟩
      (r k + r q) + r q * A[ q , k ]
        ≈⟨ +-assoc _ _ _ ⟩
      r k + (r q + r q * A[ q , k ])
        ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
      r k + r q
        ≈⟨ pcorrect-lemma ctd {lt} k q k∈vs (head∉visited ctd) ⟩
      r k
    ∎
    where
      r  = estimate ctd {≤-step′ lt}
      r′ = estimate (suc ctd) {lt}
      q  = Sorted.head _ (queue ctd {lt})
