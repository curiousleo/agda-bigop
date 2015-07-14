open import Dijkstra.Algebra

module Dijkstra.Properties
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Dijkstra.Algebra.Properties
open import Dijkstra.Algorithm alg
open import Dijkstra.Adjacency alg

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Countdown
open import Data.Fin.Properties using (_≟_; to-from; inject₁-lemma; bounded)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Matrix
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
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

module _ {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open UsingAdj i adj

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

  correct-step : {t : Fin n} (ctd : ⌛ (suc t)) → ∀ j → (j∈visited : j ∈ visited ctd) → RLS ctd j → RLS (tick ctd) j
  correct-step ctd j j∈visited rls = let open EqR setoid in
    begin
      r j + r q * A[ q , j ]
        ≈⟨ +-cong rls (*-cong eq refl) ⟩
      (I[ i , j ] + (⨁[ q ← qs ] (r j + r q * A[ q , j ]))) + r′ q * A[ q , j ]
        ≈⟨ +-cong (+-cong refl (fold-cong _ _ qs (λ q q∈qs → +-cong (eq′ j j∈visited) (*-cong (eq′ q q∈qs) refl)))) refl ⟩
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

      eq′ : ∀ j → j ∈ visited ctd → r j ≈ r′ j
      eq′ j j∈queue = {!!}
