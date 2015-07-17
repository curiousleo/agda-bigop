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
import Data.Vec.Sorted as Sorted

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)

open import Function using (_$_; _∘_; flip)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Bigop.SubsetCore +-commutativeMonoid

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open Algorithm-UsingAdj i adj

  visited-nonempty : (ctd : ℕ) {lt : ctd N≤ n} → Nonempty (visited ctd {lt})
  visited-nonempty zero      = Sub.⁅i⁆-nonempty i
  visited-nonempty (suc ctd) = Sub.∪-nonempty¹ _ _ (visited-nonempty ctd)

  visited-preserved : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ {j} → j ∈ visited ctd → j ∈ visited (suc ctd) {lt}
  visited-preserved ctd {lt} {j} j∈visited = Sub.∈∪ j (visited ctd) ⁅ head (queue ctd) ⁆ j∈visited
    where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

  visited-preserved′ : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ {j} → j ∈ visited (suc ctd) {lt} → j ≡ Sorted.head _ (queue ctd) ⊎ j ∈ visited ctd
  visited-preserved′ ctd {lt} {j} j∈vs′ with Sub.∪-∈ j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈vs′
  ... | inj₁ j∈visited = inj₂ j∈visited
  ... | inj₂ j∈⁅q⁆     = inj₁ (Sub.i∈⁅i⁆′ _ _ j∈⁅q⁆)

  start-visited : (ctd : ℕ) {lt : ctd N≤ n} → i ∈ visited ctd {lt}
  start-visited zero      {lt} = Sub.i∈⁅i⁆ i
  start-visited (suc ctd) {lt} = Sub.∪-∈′ i _ _ (start-visited ctd)

  start-visited′ : ∀ j → j ∈ visited zero {z≤n} → j ≡ i
  start-visited′ j j∈visited = Sub.i∈⁅i⁆′ i j j∈visited

  estimate-decreases : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → estimate (suc ctd) {lt} j ≤ estimate ctd j
  estimate-decreases ctd {lt} j = _ , refl

  q-minimum : (ctd : ℕ) {lt : suc ctd N≤ n} →
              let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
              estimate (suc ctd) {lt} (head (queue ctd)) ≈ estimate ctd (head (queue ctd {lt}))
  q-minimum ctd = +-absorbs-* _ _

  q-minimum′ : (ctd : ℕ) {lt : suc ctd N≤ n} →
               ∀ {j} → j ≡ Sorted.head _ (queue ctd {lt}) → estimate ctd j ≈ estimate (suc ctd) j
  q-minimum′ ctd {lt} {j} j≡q =
    begin
      r j                     ≡⟨ P.cong r j≡q ⟩
      r q                     ≈⟨ sym (+-absorbs-* _ _) ⟩
      r q + r q * A[ q , j ]  ≡⟨ P.cong₂ _+_ (P.sym (P.cong r j≡q)) P.refl ⟩
      r j + r q * A[ q , j ]
    ∎
    where
      open EqR setoid
      r  = estimate ctd
      q = Sorted.head _ (queue ctd)

  i-estimate : (ctd : ℕ) {lt : ctd N≤ n} → estimate ctd {lt} i ≈ 1#
  i-estimate zero      = reflexive (Adj.diag adj i)
  i-estimate (suc ctd) = trans (+-cong (i-estimate ctd) refl) (proj₁ +-zero _)

  visited-queue : (ctd : ℕ) {lt : ctd N≤ n} →
                  ∀ j → j ∈ visited ctd {lt} → j ≡ i ⊎ ∃₂ λ k k<n → j ≡ Sorted.head _ (queue k {k<n})
  visited-queue zero      {lt} j j∈visited = inj₁ (Sub.i∈⁅i⁆′ i j j∈visited)
  visited-queue (suc ctd) {lt} j j∈visited with Sub.∪-∈ j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈visited
  ... | inj₁ j∈vs  = visited-queue ctd j j∈vs
  ... | inj₂ j∈⁅q⁆ = inj₂ (ctd , (lt , Sub.i∈⁅i⁆′ (Sorted.head _ (queue ctd)) j j∈⁅q⁆))

  start-minimum : (ctd : ℕ) {lt : suc ctd N≤ n} →
                  ∀ j → j ≡ i → estimate (suc ctd) {lt} j ≈ estimate ctd {≤-step′ lt} j
  start-minimum ctd {lt} j j≡i rewrite j≡i | Adj.diag adj i = trans (i-estimate (suc ctd)) (sym (i-estimate ctd))

  start≢head : (ctd : ℕ) {lt : suc ctd N≤ n} → i ≢ Sorted.head _ (queue ctd {lt})
  start≢head ctd {lt} eq = head∉visited ctd (P.subst (λ x → x ∈ (visited ctd)) eq (start-visited ctd))
