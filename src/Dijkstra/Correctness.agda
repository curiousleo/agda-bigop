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

  open Algorithm-UsingAdj {n} i adj
--  open Properties-UsingAdj {n} i adj

  pRLS : (ctd : ℕ) {lt : suc ctd N≤ n} → Pred (Fin (suc n)) _
  pRLS ctd {lt} j = let r′ = estimate (suc ctd) {lt} in
    r′ j ≈ I[ i , j ] + (⨁[ k ← visited ctd {≤-step′ lt} ] (r′ j + r′ k * A[ k , j ]))

  RLS : (ctd : ℕ) {lt : ctd N≤ n} → Pred (Fin (suc n)) _
  RLS ctd {lt} j = let r = estimate ctd {lt} in
    r j ≈ I[ i , j ] + (⨁[ k ← ⊤ ] (r j + r k * A[ k , j ]))

  closer : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → j ∈ visited ctd {≤-step′ lt} →
           estimate ctd {≤-step′ lt} j ≤ estimate ctd {≤-step′ lt} (Sorted.head _ (queue ctd {lt}))
  closer zero      {lt} j j∈v = {!!} , {!!}
  closer (suc ctd) {lt} j j∈v = {!!}

  queue-head : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → j ∉ visited ctd {≤-step′ lt} → estimate ctd {≤-step′ lt} (Sorted.head _ (queue ctd {lt})) ≤ estimate ctd {≤-step′ lt} j
  queue-head ctd {lt} j j∉v = {!!}

  correct : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → pRLS ctd {lt} j
  correct zero      {lt} j = {!!}
  correct (suc ctd) {lt} j =
    begin
      r′ j
        ≡⟨⟩
      r j + r q′ * A[ q′ , j ]
        ≈⟨ +-cong (correct ctd {≤-step′ lt} j) (sym (+-idempotent _)) ⟩
      (I[ i , j ] + (⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r j + r k * A[ k , j ]))) + (r q′ * A[ q′ , j ] + r q′ * A[ q′ , j ])
        ≈⟨ +-assoc _ _ _ ⟩
      I[ i , j ] + ((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r j + r k * A[ k , j ])) + (r q′ * A[ q′ , j ] + r q′ * A[ q′ , j ]))
        ≈⟨ +-cong refl (+-cong (fold-distr′ +-idempotent f (r j) (visited ctd {≤-step′ (≤-step′ lt)}) {!visited-nonempty ctd!}) refl) ⟩
      I[ i , j ] + ((r j + (⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r k * A[ k , j ]))) + (r q′ * A[ q′ , j ] + r q′ * A[ q′ , j ]))
        ≈⟨ +-cong refl (+-cong (+-comm _ _) refl) ⟩
      I[ i , j ] + (((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r k * A[ k , j ])) + r j) + (r q′ * A[ q′ , j ] + r q′ * A[ q′ , j ]))
        ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
      I[ i , j ] + ((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r k * A[ k , j ])) + (r j + (r q′ * A[ q′ , j ] + r q′ * A[ q′ , j ])))
        ≈⟨ +-cong refl (+-cong refl (sym (+-assoc _ _ _))) ⟩
      I[ i , j ] + ((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r k * A[ k , j ])) + ((r j + r q′ * A[ q′ , j ]) + r q′ * A[ q′ , j ]))
        ≡⟨⟩
      I[ i , j ] + ((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r k * A[ k , j ])) + (r′ j + r q′ * A[ q′ , j ]))
        ≈⟨ +-cong refl (sym (+-assoc _ _ _)) ⟩
      I[ i , j ] + (((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r k * A[ k , j ])) + r′ j) + r q′ * A[ q′ , j ])
        ≈⟨ {!!} ⟩
      I[ i , j ] + (((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r′ k * A[ k , j ])) + r′ j) + r′ q′ * A[ q′ , j ])
        ≈⟨ +-cong refl (+-cong (+-comm _ _) (sym (fold-⁅i⁆ f′ q′))) ⟩
      I[ i , j ] + ((r′ j + (⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r′ k * A[ k , j ]))) + (⨁[ k ← ⁅ q′ ⁆ ] (r′ k * A[ k , j ])))
        ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
      I[ i , j ] + (r′ j + ((⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ] (r′ k * A[ k , j ])) + (⨁[ k ← ⁅ q′ ⁆ ] (r′ k * A[ k , j ]))))
        ≈⟨ +-cong refl (+-cong refl (sym (fold-∪ +-idempotent f′ (visited ctd) ⁅ q′ ⁆))) ⟩
      I[ i , j ] + (r′ j + (⨁[ k ← visited ctd {≤-step′ (≤-step′ lt)} ∪ ⁅ q′ ⁆ ] (r′ k * A[ k , j ])))
        ≈⟨ +-cong refl (sym (fold-distr′ +-idempotent f′ (r′ j) (visited ctd ∪ ⁅ q′ ⁆) {!visited-nonempty (suc ctd)!})) ⟩
      I[ i , j ] + (⨁[ k ← visited ctd ∪ ⁅ q′ ⁆ ] (r′ j + r′ k * A[ k , j ]))
        ≈⟨ {!visited (suc ctd) {≤-step′ lt}!} ⟩
      I[ i , j ] + (⨁[ k ← visited ctd ∪ ⁅ q ⁆ ] (r′ j + r′ k * A[ k , j ]))
        ≡⟨⟩
      I[ i , j ] + (⨁[ k ← visited (suc ctd) {≤-step′ lt} ] (r′ j + r′ k * A[ k , j ]))
    ∎
    where
      open EqR setoid
      r′ = estimate (suc (suc ctd)) {lt}
      r  = estimate (suc ctd) {≤-step′ lt}
      q′ = Sorted.head _ (queue (suc ctd) {lt})
      q  = Sorted.head _ (queue ctd {≤-step′ lt})
      f  = λ k → r k * A[ k , j ]
      f′ = λ k → r′ k * A[ k , j ]
  {-
  correct 0               {lt} j = {!!}
  correct 1               {lt} j = {!!}
  correct (suc (suc ctd)) {lt} j =
    begin
      estimate {!suc (suc (suc ctd))!} j
        ≈⟨ {!!} ⟩
      {!!}
    ∎
    where
      open EqR setoid
-}
  {-
    begin
      estimate (suc (suc (suc ctd))) j
        ≈⟨ ? ⟩ {-
        ≡⟨⟩
      r j + r q * A[ q , j ]
        ≈⟨ +-cong (correct ctd j) refl ⟩
      (I[ i , j ] + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ]))) + r q * A[ q , j ]
        ≈⟨ +-cong refl (sym (fold-⁅i⁆ _ q)) ⟩
      (I[ i , j ] + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ]))) + (⨁[ k ← ⁅ q ⁆ ] (r k * A[ k , j ]))
        ≈⟨ +-assoc _ _ _ ⟩
      I[ i , j ] + ((⨁[ k ← visited ctd ] (r j + r k * A[ k , j ])) + (⨁[ k ← ⁅ q ⁆ ] (r k * A[ k , j ])))
        ≈⟨ {!!} ⟩
      I[ i , j ] + ((⨁[ k ← visited ctd ] (r j + r k * A[ k , j ])) + (⨁[ k ← ⁅ q ⁆ ] (r j + r k * A[ k , j ])))
        ≈⟨ +-cong refl (sym (fold-∪ +-idempotent _ (visited ctd) ⁅ q ⁆)) ⟩
      I[ i , j ] + (⨁[ k ← visited ctd ∪ ⁅ q ⁆ ] (r j + r k * A[ k , j ]))
        ≈⟨ +-cong refl (fold-cong _ _ (visited (suc ctd)) (λ i i∈vs′ → +-cong {!!} (*-cong {!!} refl))) ⟩
-}
      I[ i , j ] + (⨁[ k ← visited (suc (suc ctd)) ] (r′ j + r′ k * A[ k , j ]))
    ∎
    where
      open EqR setoid
      r′ = estimate (suc (suc (suc ctd)))
      r  = estimate (suc (suc ctd))
      q  = Sorted.head _ (queue (suc ctd))
-}
{-
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

  correct-init : ∀ j → pRLS zero {z≤n} j
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
          r = estimate zero {z≤n}
-}
{-
  correct-q : (ctd : ℕ) {lt : suc ctd N≤ n} → pRLS ctd {≤-step′ lt} (Sorted.head _ (queue ctd {lt}))

  correct-q zero {lt} with i ≟ Sorted.head _ (queue zero)
  ... | yes i≡q =
    begin
      A[ i , q ]                                               ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) (P.sym i≡q) ⟩
      A[ i , i ]                                               ≡⟨ Adj.diag adj i ⟩
      1#                                                       ≈⟨ sym (proj₁ +-zero _) ⟩
      1#         + (⨁[ k ← ⁅ i ⁆ ] (r q + r k * A[ k , q ]))  ≡⟨ P.cong₂ _+_ (P.sym (Adj.diag I i)) P.refl ⟩
      I[ i , i ] + (⨁[ k ← ⁅ i ⁆ ] (r q + r k * A[ k , q ]))  ≡⟨ P.cong₂ _+_ (P.cong₂ I[_,_] (P.refl {x = i}) i≡q) P.refl ⟩
      I[ i , q ] + (⨁[ k ← ⁅ i ⁆ ] (r q + r k * A[ k , q ]))
    ∎
    where
      open EqR setoid
      q = Sorted.head _ (queue zero {lt})
      r = estimate zero {z≤n}

  ... | no ¬i≡q =
    begin
                            A[ i , q ]                                 ≈⟨ sym (+-idempotent _) ⟩
                            A[ i , q ] +              A[ i , q ]       ≈⟨ sym (proj₁ +-identity _) ⟩
      0#                 + (A[ i , q ] +              A[ i , q ])      ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i q ¬i≡q)) P.refl ⟩
      diagonal 0# 1# i q + (A[ i , q ] +              A[ i , q ])      ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i q)) P.refl ⟩
      I[ i , q ]         + (A[ i , q ] +              A[ i , q ])      ≈⟨ +-cong refl (+-cong refl (sym (*-identityˡ _))) ⟩
      I[ i , q ]         + (r q        + 1#         * A[ i , q ])      ≡⟨ P.cong₂ _+_ P.refl (P.cong₂ _+_ P.refl (P.cong₂ _*_ (P.sym (Adj.diag adj i)) P.refl)) ⟩
      I[ i , q ]         + (r q        + A[ i , i ] * A[ i , q ])      ≈⟨ +-cong refl (sym (fold-⁅i⁆ _ i)) ⟩
      I[ i , q ]         + (⨁[ k ← ⁅ i ⁆ ] (r q + r k * A[ k , q ]))
    ∎
    where
      open EqR setoid
      r = estimate zero {z≤n}
      q = Sorted.head _ (queue zero)

  correct-q (suc ctd) {lt} =
    begin
      r q′ + r q * A[ q , q′ ]
        ≈⟨ +-cong refl (*-cong (correct-q ctd) refl) ⟩
      r q′ + (I[ i , q ] + (⨁[ k ← qs ] (r q + r k * A[ k , q ]))) * A[ q , q′ ]
        ≡⟨ {!!} ⟩
      r q′ + (⨁[ k ← qs ] (r q + r k * A[ k , q ])) * A[ q , q′ ]
        ≈⟨ {!!} ⟩
      r q′ + (r q + (⨁[ k ← qs ] (r k * A[ k , q ]))) * A[ q , q′ ]
        ≈⟨ {!+-selective!} ⟩
      (r q′ + r q * A[ q , q′ ]) + (⨁[ k ← qs ] ((r k + r q * A[ q , k ]) * A[ k , q′ ]))
        ≡⟨⟩
      r′ q′ + (⨁[ k ← qs ] (r′ k * A[ k , q′ ]))
        ≈⟨ +-cong (sym (+-absorbs-* _ _)) refl ⟩
      (r′ q′ + r′ q′ * A[ q′ , q′ ]) + (⨁[ k ← qs ] (r′ k * A[ k , q′ ]))
        ≈⟨ +-assoc _ _ _ ⟩
      r′ q′ + (r′ q′ * A[ q′ , q′ ] + (⨁[ k ← qs ] (r′ k * A[ k , q′ ])))
        ≈⟨ +-cong refl (+-comm _ _) ⟩
      r′ q′ + ((⨁[ k ← qs ] (r′ k * A[ k , q′ ])) + r′ q′ * A[ q′ , q′ ])
        ≈⟨ +-cong refl (+-cong refl (sym (fold-⁅i⁆ (λ k → r′ k * A[ k , q′ ]) q′))) ⟩
      r′ q′ + ((⨁[ k ← qs ] (r′ k * A[ k , q′ ])) + (⨁[ k ← ⁅ q′ ⁆ ] (r′ k * A[ k , q′ ])))
        ≈⟨ +-cong refl (sym (fold-∪ +-idempotent _ (visited ctd) ⁅ q′ ⁆)) ⟩
      r′ q′ + (⨁[ k ← qs ∪ ⁅ q′ ⁆ ] (r′ k * A[ k , q′ ]))
        ≡⟨ P.cong₂ _+_ P.refl (P.cong (⨁-syntax _) (P.sym qs′-eq)) ⟩
      r′ q′ + (⨁[ k ← qs′ ] (r′ k * A[ k , q′ ]))
        ≈⟨ sym (proj₁ +-identity _) ⟩
      0# + (r′ q′ + (⨁[ k ← qs′ ] (r′ k * A[ k , q′ ])))
        ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i q′ (start≢head (suc ctd) {lt}))) P.refl ⟩
      diagonal 0# 1# i q′ + (r′ q′ + (⨁[ k ← qs′ ] (r′ k * A[ k , q′ ])))
        ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i q′)) P.refl ⟩
      I[ i , q′ ] + (r′ q′ + (⨁[ k ← qs′ ] (r′ k * A[ k , q′ ])))
        ≈⟨ +-cong refl (sym (fold-distr′ +-idempotent _ (r′ q′) qs′ (visited-nonempty (suc ctd)))) ⟩
      I[ i , q′ ] + (⨁[ k ← qs′ ] (r′ q′ + r′ k * A[ k , q′ ]))
    ∎
    where
      q  = Sorted.head _ (queue ctd)
      q′ = Sorted.head _ (queue (suc ctd) {lt})
      r  = estimate ctd
      r′ = estimate (suc ctd) {≤-step′ lt}
      open EqR setoid
      qs  = visited ctd {≤-step′ (≤-step′ lt)}
      qs′ = visited (suc ctd)

      qs′-eq : qs′ ≡ qs ∪ ⁅ q′ ⁆
      qs′-eq = {!P.refl!}
-}

{-
  estimate-preserved : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → j ∈ visited (suc ctd) {lt} →
                       estimate ctd {≤-step′ lt} j ≈ estimate (suc ctd) {lt} j
  estimate-preserved ctd       {lt} j j∈vs″ with visited-preserved′ ctd {lt} j∈vs″
  estimate-preserved ctd       {lt} j j∈vs″ | inj₁ j≡q   = q-minimum′ ctd {lt} j≡q
  estimate-preserved zero      {lt} j j∈vs″ | inj₂ j∈vs′ = sym (start-minimum zero {lt} j (start-visited′ j j∈vs′))
  estimate-preserved (suc ctd) {lt} j j∈vs″ | inj₂ j∈vs′ with visited-preserved′ ctd j∈vs′
  estimate-preserved (suc ctd) {lt} j j∈vs″ | inj₂ j∈vs′ | inj₁ j≡q  = ?
  estimate-preserved (suc ctd) {lt} j j∈vs″ | inj₂ j∈vs′ | inj₂ j∈vs = ?
    {-
      where
        q = Sorted.head _ (queue (suc ctd))
        r′ = estimate (suc ctd)
        r = estimate ctd
        {-
        open EqR setoid
        -- r′ = estimate (suc (suc ctd))

        eq : r j + r q * A[ q , j ] ≈ r j
        eq =
          begin
            r′ j + r′ q * A[ q , j ]
              ≈⟨ +-cong ? refl ⟩
            r j + r′ q * A[ q , j ]
              ≈⟨ ? ⟩
            (I[ i , j ] + (⨁[ q ← visited ctd {lt} ] (r j + r q * A[ q , j ]))) + r′ q * A[ q , j ]
              ≈⟨ ? ⟩
            r′ j
          ∎ -}
    -}
-}
{-
    correct-step : (ctd : ℕ) {lt : ctd N≤ n} → ∀ j → j ∈ visited ctd {lt} → pRLS ctd {lt} j

    correct-step zero j j∈visited =
      begin
        A[ i , j ]                                               ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) (start-visited′ j j∈visited) ⟩
        A[ i , i ]                                               ≡⟨ Adj.diag adj i ⟩
        1#                                                       ≈⟨ sym (proj₁ +-zero _) ⟩
        1#         + (⨁[ k ← ⁅ i ⁆ ] (r j + r k * A[ k , j ]))  ≡⟨ P.cong₂ _+_ (P.sym (Adj.diag I i)) P.refl ⟩
        I[ i , i ] + (⨁[ k ← ⁅ i ⁆ ] (r j + r k * A[ k , j ]))  ≡⟨ P.cong₂ _+_ (P.cong₂ I[_,_] (P.refl {x = i}) (P.sym (start-visited′ j j∈visited))) P.refl ⟩
        I[ i , j ] + (⨁[ k ← ⁅ i ⁆ ] (r j + r k * A[ k , j ]))
      ∎
      where
        open EqR setoid
        r = estimate zero {z≤n}

    correct-step (suc ctd) {lt} j j∈visited′ with visited-preserved′ ctd j∈visited′
    ... | inj₁ j≡q =
      begin
        r′ j
          ≈⟨ refl ⟩
        r j + r q * A[ q , j ]
          ≈⟨ +-cong refl (*-cong (sym (reflexive (P.cong r j≡q))) refl) ⟩
        r j + r j * A[ q , j ]
          ≈⟨ +-absorbs-* _ _ ⟩
        r j
          ≈⟨ correct-step ctd j {!!} ⟩
        I[ i , j ] + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ]))
          ≈⟨ +-cong refl (fold-distr′ +-idempotent _ (r j) (visited ctd) (visited-nonempty ctd)) ⟩
        I[ i , j ] + (r j + (⨁[ k ← visited ctd ] (r k * A[ k , j ])))
          ≈⟨ +-cong refl (+-cong (sym (+-idempotent _)) refl) ⟩
        I[ i , j ] + ((r j + r j) + (⨁[ k ← visited ctd ] (r k * A[ k , j ])))
          ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
        I[ i , j ] + (r j + (r j + (⨁[ k ← visited ctd ] (r k * A[ k , j ]))))
          ≈⟨ +-cong refl (+-cong refl (sym (fold-distr′ +-idempotent _ (r j) (visited ctd) (visited-nonempty ctd)))) ⟩
        I[ i , j ] + (r j + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ])))
          ≈⟨ +-cong refl (+-cong (sym (+-absorbs-* _ _)) refl) ⟩
        I[ i , j ] + ((r j + r j * A[ q , j ]) + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ])))
          ≈⟨ +-cong refl (+-cong (+-cong refl (*-cong (reflexive (P.cong r j≡q)) refl)) refl) ⟩
        I[ i , j ] + ((r j + r q * A[ q , j ]) + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ])))
          ≈⟨ ? ⟩
        I[ i , j ] + ((⨁[ k ← ⁅ q ⁆ ] (r j + r k * A[ k , j ])) + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ])))
          ≈⟨ +-cong refl (sym {!!}) ⟩
        I[ i , j ] + (⨁[ k ← visited ctd ∪ ⁅ q ⁆ ] (r j + r k * A[ k , j ]))
          ≈⟨ {!!} ⟩
        I[ i , j ] + (⨁[ k ← visited (suc ctd) ] (r′ j + r′ k * A[ k , j ]))
      ∎
      where
        open EqR setoid
        q = Sorted.head _ (queue ctd)
        r = estimate ctd
        r′ = estimate (suc ctd)
        
    ... | inj₂ j∈visited = let open EqR setoid in
      begin
        r j + r q * A[ q , j ]
          ≈⟨ +-cong (correct-step ctd j j∈visited) (*-cong (sym (q-minimum ctd)) refl) ⟩
        (I[ i , j ] + (⨁[ q ← qs ] (r j + r q * A[ q , j ]))) + r′ q * A[ q , j ]
          ≈⟨ +-cong (+-cong refl (fold-cong _ _ qs (λ q q∈qs → +-cong {!estimate-preserved ctd j ?!} (*-cong (sym {!q-minimum ctd!}) refl)))) refl ⟩
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
-}
{-
  visited-minimum : (ctd : ℕ) {lt : ctd < n} →
                    ∀ j → j ∈ visited ctd {≤-step lt} → estimate (suc ctd) {s≤s lt} j ≈ estimate ctd {≤-step lt} j
  visited-minimum ctd {lt} j j∈visited with visited-queue ctd {≤-step lt} j j∈visited
  ... | inj₁ j≡i               = start-minimum ctd j j≡i
  ... | inj₂ (k , (k<n , j≡q)) = trans (reflexive (P.cong (estimate (suc ctd)) j≡q)) {!q-minimum ctd {k<n}!}
-}
