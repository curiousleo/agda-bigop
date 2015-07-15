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
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.MoreProperties
open import Data.Nat.Properties using (≤-step)
open import Data.Product using (proj₁; proj₂; _,_; ∃; ∃₂)
open import Data.Sum
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open import Function using (_$_; _∘_)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Bigop.SubsetCore +-commutativeMonoid

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open Algorithm-UsingAdj i adj

  RLS : (ctd : ℕ) {lt : ctd < suc n} → Pred (Fin (suc n)) _
  RLS ctd {lt} j = let r = estimate ctd {lt} in
    r j ≈ I[ i , j ] + (⨁[ q ← visited ctd {lt} ] (r j + r q * A[ q , j ]))

  init‿A≈I+A : (i j : Fin (suc n)) → A[ i , j ] ≈ I[ i , j ] + A[ i , j ]
  init‿A≈I+A i j with i ≟ j
  ... | yes i≡j rewrite i≡j = let open EqR setoid in
    begin
      A[ j , j ]               ≡⟨ Adj.diag adj j ⟩
      1#                       ≈⟨ sym (+-idempotent _) ⟩
      1#         + 1#          ≡⟨ P.sym (P.cong₂ _+_ (Adj.diag I j) (Adj.diag adj j)) ⟩
      I[ j , j ] + A[ j , j ]
    ∎
  ... | no ¬i≡j = let open EqR setoid in
    begin
      A[ i , j ]                       ≈⟨ sym (proj₁ +-identity _) ⟩
      0#                 + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl ⟩
      diagonal 0# 1# i j + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl ⟩
      I[ i , j ]         + A[ i , j ]
    ∎

  correct-init : ∀ j → RLS zero {s≤s z≤n} j
  correct-init j = trans (init‿A≈I+A i j) (+-cong refl lemma)
    where
      lemma =
        begin
          A[ i , j ]
            ≈⟨ sym (+-idempotent _) ⟩
          A[ i , j ] + A[ i , j ]
            ≈⟨ +-cong refl (sym (*-identityˡ _)) ⟩
          A[ i , j ] + 1# * A[ i , j ]
            ≈⟨ +-cong refl (*-cong (sym (reflexive (Adj.diag adj i))) refl) ⟩
          A[ i , j ] + A[ i , i ] * A[ i , j ]
            ≡⟨⟩
          r j + r i * A[ i , j ]
            ≈⟨ sym (fold-⁅i⁆ _ i) ⟩
          ⨁[ q ← ⁅ i ⁆ ] (r j + r q * A[ q , j ])
        ∎
        where
          open EqR setoid
          r = estimate zero {s≤s z≤n}

  visited-nonempty : (ctd : ℕ) {lt : ctd < suc n} → Nonempty (visited ctd {lt})
  visited-nonempty zero      = Sub.⁅i⁆-nonempty i
  visited-nonempty (suc ctd) = Sub.∪-nonempty¹ _ _ (visited-nonempty ctd)

  visited-preserved : (ctd : ℕ) {lt : ctd < n} → ∀ {j} → j ∈ visited ctd → j ∈ visited (suc ctd) {s≤s lt}
  visited-preserved ctd {lt} {j} j∈visited = Sub.∈∪ j (visited ctd) ⁅ head (queue ctd) ⁆ j∈visited
    where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

  start-visited : ∀ j → j ∈ visited zero {s≤s z≤n} → j ≡ i
  start-visited j j∈visited = Sub.i∈⁅i⁆′ i j j∈visited

  estimate-decreases : (ctd : ℕ) {lt : ctd < n} →
                       ∀ j → estimate (suc ctd) {s≤s lt} j ≤ estimate ctd j
  estimate-decreases ctd {lt} j = _ , refl

  q-minimum : (ctd : ℕ) {lt : ctd < n} →
              let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
              estimate (suc ctd) {s≤s lt} (head (queue ctd)) ≈ estimate ctd (head (queue ctd))
  q-minimum ctd = +-absorbs-* _ _

  visited-queue : (ctd : ℕ) {lt : ctd < suc n} →
                  ∀ j → j ∈ visited ctd {lt} → j ≡ i ⊎ ∃₂ λ k k<n → j ≡ Sorted.head _ (queue k {k<n})
  visited-queue zero      {lt} j j∈visited = inj₁ (Sub.i∈⁅i⁆′ i j j∈visited)
  visited-queue (suc ctd) {lt} j j∈visited with Sub.∪-∈ j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈visited
  ... | inj₁ j∈vs  = visited-queue ctd j j∈vs
  ... | inj₂ j∈⁅q⁆ = inj₂ (ctd , (suc-inj lt , Sub.i∈⁅i⁆′ (Sorted.head _ (queue ctd)) j j∈⁅q⁆))

  start-minimum : ∀ j → j ≡ i → estimate (suc zero) {{!suc zero < suc n!}} j ≈ estimate zero {s≤s z≤n} j
  start-minimum j j≡i rewrite j≡i | Adj.diag adj i = proj₁ +-zero _

  visited-minimum : (ctd : ℕ) {lt : ctd < suc n} →
                    ∀ j → j ∈ visited ctd {lt} → estimate (suc ctd) j ≈ estimate ctd j
  visited-minimum ctd {lt} j j∈visited with visited-queue ctd {lt} j j∈visited
  ... | inj₁ j≡i               = {!start-minimum j j≡i!}
  ... | inj₂ (k , (k<n , j≡q)) = {!q-minimum !}

  correct-step : (ctd : ℕ) {lt : ctd < n} → ∀ j → j ∈ visited ctd {≤-step lt} → RLS ctd j → RLS (suc ctd) {s≤s lt} j
  correct-step ctd j j∈visited rls = let open EqR setoid in
    begin
      r j + r q * A[ q , j ]
        ≈⟨ +-cong rls (*-cong {!!} refl) ⟩
      (I[ i , j ] + (⨁[ q ← qs ] (r j + r q * A[ q , j ]))) + r′ q * A[ q , j ]
        ≈⟨ +-cong (+-cong refl (fold-cong _ _ qs (λ q q∈qs → +-cong {!estimate-preserved ctd j∈visited!} (*-cong {!estimate-preserved ctd q∈qs!} refl)))) refl ⟩
      (I[ i , j ] + (⨁[ q ← qs ] (r′ j + r′ q * A[ q , j ]))) + r′ q * A[ q , j ]
        ≈⟨ +-assoc _ _ _ ⟩
      I[ i , j ] + ((⨁[ q ← qs ] (r′ j + r′ q * A[ q , j ])) + r′ q * A[ q , j ])
        ≈⟨ +-cong refl (+-cong (fold-distr′ +-idempotent _ (r′ j) qs (visited-nonempty ctd)) refl) ⟩
      I[ i , j ] + ((r′ j + ((⨁[ q ← qs ] (r′ q * A[ q , j ]))) + r′ q * A[ q , j ]))
        ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
      I[ i , j ] + (r′ j + ((⨁[ q ← qs ] (r′ q * A[ q , j ])) + r′ q * A[ q , j ]))
        ≈⟨ +-cong refl (+-cong refl (+-cong refl (sym (fold-⁅i⁆ _ q)))) ⟩
      I[ i , j ] + (r′ j + ((⨁[ q ← qs ] (r′ q * A[ q , j ])) + (⨁[ q ← ⁅ q ⁆ ] (r′ q * A[ q , j ]))))
        ≈⟨ +-cong refl (+-cong refl (sym (fold-∪ +-idempotent _ (visited ctd) ⁅ q ⁆))) ⟩
      I[ i , j ] + (r′ j + (⨁[ q ← qs′ ] (r′ q * A[ q , j ])))
        ≈⟨ +-cong refl (sym (fold-distr′ +-idempotent _ (r′ j) qs′ (visited-nonempty (suc ctd)))) ⟩
      I[ i , j ] + (⨁[ q ← qs′ ] (r′ j + r′ q * A[ q , j ]))
    ∎
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd) hiding (_∈_)
      r = estimate ctd
      r′ = estimate (suc ctd)
      q = head (queue ctd)
      qs = visited ctd
      qs′ = visited ctd ∪ ⁅ q ⁆
