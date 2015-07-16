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

  RLS : (ctd : ℕ) {lt : ctd N≤ n} → Pred (Fin (suc n)) _
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

  correct-init : ∀ j → RLS zero {z≤n} j
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

  visited-nonempty : (ctd : ℕ) {lt : ctd N≤ n} → Nonempty (visited ctd {lt})
  visited-nonempty zero      = Sub.⁅i⁆-nonempty i
  visited-nonempty (suc ctd) = Sub.∪-nonempty¹ _ _ (visited-nonempty ctd)

  visited-preserved : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ {j} → j ∈ visited ctd → j ∈ visited (suc ctd) {lt}
  visited-preserved ctd {lt} {j} j∈visited = Sub.∈∪ j (visited ctd) ⁅ head (queue ctd) ⁆ j∈visited
    where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

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

{-
  correct-q : (ctd : ℕ) {lt : suc ctd N≤ n} → RLS ctd {≤-step′ lt} (Sorted.head _ (queue ctd {lt}))

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
--      lemma₀ : estimate (suc ctd) (Sorted.head _ (queue ctd)) ≈ estimate ctd (Sorted.head _ (queue ctd))
--      lemma₀ = q-minimum ctd {suc-inj (≤-step lt)}

  mutual

    estimate-preserved : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j → j ∈ visited ctd {≤-step′ lt} →
                         estimate ctd {≤-step′ lt} j ≈ estimate (suc ctd) {lt} j

    estimate-preserved zero {lt} j j∈visited = {!!}

    estimate-preserved (suc ctd) {lt} j j∈visited = {!!} {- trans (correct-step ctd j j∈visited) (sym eq)
      where
        open EqR setoid
        r = estimate ctd
        r′ = estimate (suc ctd)

        eq =
          begin
            r j + r k * A[ k , j ]
              ≈⟨ {!correct-step (suc ctd) j ?!} ⟩
            I[ i , j ] + (⨁[ k ← visited (suc ctd) ] (r′ j + r′ k * A[ k , j ]))
              ≈⟨ {!!} ⟩
            I[ i , j ] + (⨁[ k ← visited ctd ] (r j + r k * A[ k , j ]))
          ∎
-}

    correct-step : (ctd : ℕ) {lt : ctd N≤ n} → ∀ j → j ∈ visited ctd {lt} → RLS ctd {lt} j

    correct-step zero j j∈visited = {!!} {-
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
        r = estimate zero {z≤n} -}

    correct-step (suc ctd) j j∈visited = let open EqR setoid in
      begin
        r j + r q * A[ q , j ]
          ≈⟨ +-cong (correct-step ctd j {!!}) (*-cong (sym (q-minimum ctd)) refl) ⟩
        (I[ i , j ] + (⨁[ q ← qs ] (r j + r q * A[ q , j ]))) + r′ q * A[ q , j ]
          ≈⟨ +-cong (+-cong refl (fold-cong _ _ qs (λ q q∈qs → +-cong (estimate-preserved ctd j {!!}) (*-cong ? refl)))) refl ⟩
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

{-
  visited-minimum : (ctd : ℕ) {lt : ctd < n} →
                    ∀ j → j ∈ visited ctd {≤-step lt} → estimate (suc ctd) {s≤s lt} j ≈ estimate ctd {≤-step lt} j
  visited-minimum ctd {lt} j j∈visited with visited-queue ctd {≤-step lt} j j∈visited
  ... | inj₁ j≡i               = start-minimum ctd j j≡i
  ... | inj₂ (k , (k<n , j≡q)) = trans (reflexive (P.cong (estimate (suc ctd)) j≡q)) {!q-minimum ctd {k<n}!}
-}
