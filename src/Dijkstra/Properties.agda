open import Dijkstra.Algebra

module Dijkstra.Properties
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Dijkstra.Algebra.Properties
open import Dijkstra.Algorithm alg renaming (module UsingAdj to Algorithm-UsingAdj)
open import Dijkstra.Adjacency alg

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Countdown
open import Data.Fin.Properties using (_≟_; to-from; inject₁-lemma; bounded)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Matrix
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_; ∃)
open import Data.Sum
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open import Function using (_$_; _∘_; flip)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Bigop.SubsetCore +-commutativeMonoid

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open Algorithm-UsingAdj i adj

  RLS : {t : Fin (suc n)} → (ctd : ⌛ t) → Pred (Fin (suc n)) _
  RLS ctd j = let r = estimate ctd in
    r j ≈ I[ i , j ] + (⨁[ q ← visited ctd ] (r j + r q * A[ q , j ]))

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

  correct-init : ∀ j → RLS start j
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
          r = estimate start

  visited-nonempty : ∀ {t} (ctd : ⌛ t) → Nonempty (visited ctd)
  visited-nonempty start      = Sub.⁅i⁆-nonempty i
  visited-nonempty (tick ctd) = Sub.∪-nonempty¹ _ _ (visited-nonempty ctd)

  visited-preserved : {t : Fin n} (ctd : ⌛ (suc t)) → ∀ {j} → j ∈ visited ctd → j ∈ visited (tick ctd)
  visited-preserved ctd {j} j∈visited = Sub.∈∪ j (visited ctd) ⁅ head (queue ctd) ⁆ j∈visited
    where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

  start-visited : ∀ j → j ∈ visited start → j ≡ i
  start-visited j j∈visited = Sub.i∈⁅i⁆′ i j j∈visited

  [_]-optimal_wrt_ : {t : Fin (suc n)} → ⌛ t → Fin (suc n) → Fin (suc n) → Set _
  [ ctd ]-optimal j wrt q = let r = estimate ctd in r q * A[ q , j ] + r j ≈ r j

  estimate-decreases : {t : Fin n} (ctd : ⌛ (suc t)) → ∀ j → estimate (tick ctd) j ≤ estimate ctd j
  estimate-decreases ctd j = _ , refl

  q-minimum : {t : Fin n} (ctd : ⌛ (suc t)) →
              let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
              estimate (tick ctd) (head (queue ctd)) ≈ estimate ctd (head (queue ctd))
  q-minimum ctd = +-absorbs-* _ _

  visited-queue : {t : Fin n} (ctd : ⌛ (suc t)) →
                  ∀ j → j ∈ visited (tick ctd) → j ≡ i ⊎ ∃ λ k → j ≡ Sorted.head _ (queue k)
  visited-queue ctd j j∈visited with Sub.∪-∈ j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈visited
  ... | inj₁ j∈vs  = {!visited-queue ? j j∈vs!}
  ... | inj₂ i∈⁅q⁆ = {!!}

{-
  visited-queue : {t : Fin (suc n)} (ctd : ⌛ t) →
                  ∀ j → j ∈ visited ctd → j ≡ i ⊎ ∃ λ k → j ≡ Sorted.head _ (queue k)
  visited-queue start      j j∈vs = inj₁ (Sub.i∈⁅i⁆′ i j j∈vs)
  visited-queue (tick ctd) j j∈vs with Sub.∪-∈ j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈vs
  ... | inj₁ j∈vs′ = visited-queue ctd j j∈vs′
  ... | inj₂ j∈⁅q⁆ = inj₂ (ctd , (Sub.i∈⁅i⁆′ (head (queue ctd)) j j∈⁅q⁆))
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
-}

  minimum : {t : Fin n} (ctd : ⌛ (suc t)) →
            ∀ j → j ∈ visited (tick ctd) → estimate (tick ctd) j ≈ estimate ctd j
  minimum ctd j j∈visited with Sub.∪-∈ j (visited ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈visited

  minimum ctd j j∈visited | inj₁ j∈vs  =
    begin
      r j + r q * A[ q , j ]
        ≈⟨ {!minimum _ j j∈vs!} ⟩
      r j
    ∎
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
      q = head (queue ctd)
      open EqR setoid
      r = estimate ctd
      r′ = estimate (tick ctd)

  minimum ctd j j∈visited | inj₂ i∈⁅q⁆ =
    begin
      r j + r q * A[ q , j ]
        ≈⟨ +-cong (reflexive (P.cong r (Sub.i∈⁅i⁆′ q j i∈⁅q⁆))) refl ⟩
      r q + r q * A[ q , j ]
        ≈⟨ +-absorbs-* _ _ ⟩
      r q
        ≡⟨ P.cong r (P.sym (Sub.i∈⁅i⁆′ q j i∈⁅q⁆)) ⟩
      r j
    ∎
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
      q = head (queue ctd)
      open EqR setoid
      r = estimate ctd
      r′ = estimate (tick ctd)
      

{-
  estimate-optimal : {t : Fin n} (ctd : ⌛ (suc t)) →
                     let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) hiding (_∈_) in
                     ∀ j → j ∈ visited ctd → [ ctd ]-optimal j wrt (head (queue ctd))
  estimate-optimal ctd zero j∈visited = {!!}
  estimate-optimal ctd (suc j) j∈visited = {!!}
                         -- r j ≤ r q * A[ q , j ]
-}
{-
  head-queue-optimal : {t : Fin n} (ctd : ⌛ (suc t)) →
                       let open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
                       in Optimal ctd (head (queue ctd))
  head-queue-optimal ctd = {!!}

  estimate-optimal : {t : Fin (suc n)} (ctd : ⌛ t) →
                     ∀ j → j ∈ visited ctd → Optimal ctd j
  estimate-optimal start j j∈visited k k∈visited
    rewrite
      start-visited j j∈visited | start-visited k k∈visited | Adj.diag adj i
      = proj₂ +-zero _
  estimate-optimal (tick ctd) j j∈visited k k∈visited =
    begin
      r′ k * A[ k , j ] + r′ j
        ≡⟨⟩
      (r k + r q * A[ q , k ]) * A[ k , j ] + r′ j
        ≈⟨ {!!} ⟩
      (r q * A[ q , k ] + r k) * A[ k , j ] + r′ j
        ≈⟨ +-cong (*-cong (estimate-optimal ctd k {!!} q {!!}) refl) refl ⟩
      r k * A[ k , j ] + r′ j
        ≈⟨ {!!} ⟩
      r k * A[ k , j ] + r j
        ≈⟨ estimate-optimal ctd j {!j∈visited!} k {!!} ⟩
      r j
        ≈⟨ {!!} ⟩
      r′ j
    ∎
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
      q = head (queue ctd)
      open EqR setoid
      r = estimate ctd
      r′ = estimate (tick ctd)
-}
{-
  estimate-optimal : {t : Fin (suc n)} (ctd : ⌛ t) →
                     ∀ {j q} → j ∈ visited ctd → q ∈ visited ctd →
                     estimate ctd j ≤ estimate ctd q * A[ q , j ]
  estimate-optimal start {j} {q} j∈visited q∈visited = 0# , eq
    where
      open EqR setoid
      r  = estimate start

      r≡1 : ∀ j → j ∈ visited start → r j ≡ 1#
      r≡1 j j∈visited = P.trans (P.cong r (start-visited j j∈visited)) (Adj.diag adj i)

      eq =
        begin
          r j
            ≡⟨ r≡1 j j∈visited ⟩
          1#
            ≈⟨ sym (*-identityˡ _) ⟩
          1# * 1#
            ≈⟨ sym $ *-cong (reflexive (r≡1 q q∈visited)) (reflexive (Adj.diag adj i)) ⟩
          r q * A[ i , i ]
            ≈⟨ *-cong refl (sym $ reflexive (P.cong₂ A[_,_] (start-visited q q∈visited)
                                                            (start-visited j j∈visited))) ⟩
          r q * A[ q , j ]
            ≈⟨ sym (proj₂ +-identity _) ⟩
          (r q * A[ q , j ]) + 0#
        ∎
  estimate-optimal (tick ctd) {j} {k} j∈visited k∈visited = r′ j , eq
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
      q = head (queue ctd)
      open EqR setoid
      r = estimate ctd
      r′ = estimate (tick ctd)

      eq =
        begin
          r′ j
            ≡⟨⟩
          r j + r q * A[ q , j ]
            ≈⟨ {!!} ⟩
          (r′ k * A[ k , j ]) + r′ j
        ∎
-}

{-
  estimate-preserved : {t : Fin n} (ctd : ⌛ (suc t)) → ∀ {j} → j ∈ visited ctd → estimate ctd j ≈ estimate (tick ctd) j
  estimate-preserved ctd {j} j∈visited =
    begin
      r j
        ≈⟨ {!!} ⟩
      r j + r q * A[ q , j ]
        ≡⟨⟩
      r′ j
    ∎
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
      open EqR setoid
      q = head (queue ctd)
      r  = estimate ctd
      r′ = estimate (tick ctd)

  correct-step : {t : Fin n} (ctd : ⌛ (suc t)) → ∀ j → (j∈visited : j ∈ visited ctd) → RLS ctd j → RLS (tick ctd) j
  correct-step ctd j j∈visited rls = let open EqR setoid in
    begin
      r j + r q * A[ q , j ]
        ≈⟨ +-cong rls (*-cong eq refl) ⟩
      (I[ i , j ] + (⨁[ q ← qs ] (r j + r q * A[ q , j ]))) + r′ q * A[ q , j ]
        ≈⟨ +-cong (+-cong refl (fold-cong _ _ qs (λ q q∈qs → +-cong (estimate-preserved ctd j∈visited) (*-cong (estimate-preserved ctd q∈qs) refl)))) refl ⟩
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
        ≈⟨ +-cong refl (sym (fold-distr′ +-idempotent _ (r′ j) qs′ (visited-nonempty (tick ctd)))) ⟩
      I[ i , j ] + (⨁[ q ← qs′ ] (r′ j + r′ q * A[ q , j ]))
    ∎
    where
      open Sorted (estimateOrder $ V.tabulate $ estimate ctd) hiding (_∈_)
      r = estimate ctd
      r′ = estimate (tick ctd)
      q = head (queue ctd)
      qs = visited ctd
      qs′ = visited ctd ∪ ⁅ q ⁆

      eq : r q ≈ r′ q
      eq = {!q!}
-}
