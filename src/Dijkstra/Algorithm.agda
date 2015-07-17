open import Dijkstra.Algebra

module Dijkstra.Algorithm
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_≤_; _+_)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Nat hiding (_+_; _*_)
open import Data.Nat.MoreProperties
open import Data.Nat.Properties using (≤-step)
open import Data.List.Base
open import Data.Matrix
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Function using (_$_; _∘_)

open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)
import Relation.Binary.EqReasoning as EqR

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Bigop.SubsetCore +-commutativeMonoid

open DecTotalOrder Data.Nat.decTotalOrder
  using ()
  renaming (refl to ≤-refl; trans to ≤-trans)

I : ∀ {n} → Adj n
I = matrix ▦[ diag ]
  where
    matrix : Matrix Weight _ _
    matrix = tabulate (diagonal 0# 1#)

    diag : ∀ i → (matrix [ i , i ]) ≡ 1#
    diag i = P.trans (lookup∘tabulate i i) (diagonal-diag i)

I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]

---

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  A[_,_] : Fin (suc n) → Fin (suc n) → Weight
  A[ i , j ] = Adj.matrix adj [ i , j ]

  iter : ∀ (m : ℕ) {lt : suc m ≤ n} {a} {A : Set a} (f : A → A) → A → A
  iter zero    {lt} f x = x
  iter (suc m) {lt} f x = f (iter m {≤-step′ lt} f x)

  mutual

    estimate : (ctd : ℕ) {lt : ctd ≤ n} → Fin (suc n) → Weight
    estimate zero              j = I[ i , j ]
    estimate (suc ctd) {ctd≤n} j = r j + r q * A[ q , j ]
      where
        open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
        q = head (queue ctd {≤-step′ ctd≤n})
        r = estimate ctd {≤-step′ ctd≤n}

    visited : (ctd : ℕ) {lt : ctd ≤ n} → Subset (suc n)
    visited zero              = ⊥
    visited (suc ctd) {ctd≤n} = visited ctd {≤-step′ ctd≤n} ∪ ⁅ head (queue ctd {≤-step′ ctd≤n}) ⁆
      where
        open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

    visited-lemma : (ctd : ℕ) {lt : ctd ≤ n} → Sub.size (visited ctd {lt}) ≡ ctd
    visited-lemma zero           = Sub.size⊥≡0 {n}
    visited-lemma (suc ctd) {lt} =
      begin
        Sub.size (visited ctd ∪ ⁅ q ⁆)
          ≡⟨ P.cong Sub.size (∪-comm (visited ctd) ⁅ q ⁆) ⟩
        Sub.size (⁅ q ⁆ ∪ visited ctd)
          ≡⟨ Sub.size-suc q (visited ctd) (head∉visited ctd) ⟩
        suc (Sub.size (visited ctd))
          ≡⟨ P.cong suc (visited-lemma ctd) ⟩
        suc ctd
      ∎
      where
        open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
        open P.≡-Reasoning
        open Sub.Properties (suc n)
        q = head (queue ctd {≤-step′ lt})

    size-lemma : (ctd : ℕ) {lt : ctd ≤ n} → Sub.size (∁ (visited ctd {lt})) ≡ suc n ∸ ctd
    size-lemma ctd =
      begin
        Sub.size (∁ (visited ctd))      ≡⟨ Sub.∁-size (visited ctd) ⟩
        suc n ∸ Sub.size (visited ctd)  ≡⟨ P.cong₂ _∸_ P.refl (visited-lemma ctd) ⟩
        suc n ∸ ctd
      ∎
      where
        open P.≡-Reasoning

    queue′ : (ctd : ℕ) {lt : ctd ≤ n} →
             let open Sorted (estimateOrder $ V.tabulate $ estimate ctd {lt}) in
             SortedVec (Sub.size $ ∁ $ visited ctd {lt})
    queue′ ctd = fromVec $ Sub.toVec $ ∁ $ visited ctd
      where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

    queue : (ctd : ℕ) {lt : ctd ≤ n} →
            let open Sorted (estimateOrder $ V.tabulate $ estimate ctd {lt}) in
            SortedVec (suc (n ∸ ctd))
    queue ctd {ctd≤n} = P.subst SortedVec (P.trans (size-lemma ctd) (sm∸n n ctd ctd≤n)) (queue′ ctd)
      where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

    postulate
      q′→q : (ctd : ℕ) {lt : ctd ≤ n} →
             let open Sorted (estimateOrder $ V.tabulate $ estimate ctd {lt}) in
             ∀ {p} (P : ∀ {n} → SortedVec n → Set p) → P (queue′ ctd) → P (queue ctd {lt})

{-
      q′→q ctd P Pq′ = {!!}
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
-}

    head∉visited : (ctd : ℕ) {lt : ctd ≤ n} →
                   let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
                   head (queue ctd {lt}) ∉ visited ctd {lt}
    head∉visited ctd {lt} q∈vs with queue ctd {lt}
    head∉visited ctd {lt} q∈vs | q Sorted.∷ qs ⟨ q≼qs ⟩ = q∉q∷qs (S.here qs q≼qs)
      where
        module S = Sorted (estimateOrder $ V.tabulate $ estimate ctd {lt})

        postulate
          q∉queue′ : ¬ (q S.∈ (queue′ ctd))
          -- q∉queue′ = {!S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))!}

        q∉queue : ¬ (q S.∈ (queue ctd {lt}))
        q∉queue = q′→q ctd {lt} (λ qs → ¬ (q S.∈ qs)) q∉queue′

        postulate
          q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
       -- q∉q∷qs = P.subst (λ qs → ¬ q S.∈ qs) {!P.refl!} q∉queue
      -- q ∈ visited ctd
      -- ⟶ q ∉ ∁ (visited ctd)   by Sub.∁-∈
      -- ⟶ q ∉ Sub.toVec (∁ (visited ctd))   by Sub.toVec-∉¹
      -- ⟶ q ∉ fromVec (Sub.toVec (∁ (visited ctd)))   by fromVec-∉¹
      -- ⟶ q ∉ P.subst SortedVec {! eq !} (fromVec (Sub.toVec (∁ (visited ctd))))
