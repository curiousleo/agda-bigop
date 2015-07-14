open import Dijkstra.Algebra

module Dijkstra.Algorithm
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_≤_; _+_)
open import Data.Fin.Properties using (_≟_; to-from; inject₁-lemma; bounded)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
import Data.Nat as N
open N using (ℕ; zero; suc; _∸_; z≤n; s≤s)
open import Data.Nat.MoreProperties
open import Data.Nat.Properties using (n∸n≡0; ≤-step)
open import Data.List.Base
open import Data.Matrix
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Function using (_$_; _∘_; flip)

open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)
import Relation.Binary.EqReasoning as EqR

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Bigop.SubsetCore +-commutativeMonoid

open DecTotalOrder N.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

I : ∀ {n} → Adj n
I = matrix ▦[ diag ]
  where
    matrix : Matrix Weight _ _
    matrix = tabulate (diagonal 0# 1#)

    diag : ∀ i → (matrix [ i , i ]) ≡ 1#
    diag i = P.trans (lookup∘tabulate i i) (diagonal-diag i)

I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]

iter : ∀ {a} (A : ℕ → Set a) (f : {n : ℕ} → A (suc n) → A n) {n : ℕ} → A n → A zero
iter A f {zero}  x = x
iter A f {suc n} x = f (iter (A ∘ suc) f x)

---

module UsingAdj {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open import Data.Fin.Countdown

  private

    A[_,_] : Fin (suc n) → Fin (suc n) → Weight
    A[ i , j ] = Adj.matrix adj [ i , j ]

    mutual

      estimate : {t : Fin (suc n)} → ⌛ t → Fin (suc n) → Weight
      estimate start      j = A[ i , j ]
      estimate (tick ctd) j = r j + r q * A[ q , j ]
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
          q = head (queue ctd)
          r = estimate ctd

      visited : {t : Fin (suc n)} → ⌛ t → Subset (suc n)
      visited start      = ⁅ i ⁆
      visited (tick ctd) = visited ctd ∪ ⁅ head (queue ctd) ⁆
        where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      visited-lemma : {t : Fin (suc n)} (ctd : ⌛ t) → Sub.size (visited ctd) ≡ suc n ∸ (toℕ t)
      visited-lemma start rewrite to-from n | sn∸n≡1 n = Sub.size⁅i⁆≡1 i
      visited-lemma (tick {t} ctd) =
        begin
          Sub.size (visited ctd ∪ ⁅ head (queue ctd) ⁆)
            ≡⟨ P.cong Sub.size (∪-comm (visited ctd) ⁅ head (queue ctd) ⁆) ⟩
          Sub.size (⁅ head (queue ctd) ⁆ ∪ visited ctd)
            ≡⟨ Sub.size-suc (head (queue ctd)) (visited ctd) (head∉visited ctd) ⟩
          suc (Sub.size (visited ctd))
            ≡⟨ P.cong suc (visited-lemma ctd) ⟩
          suc (suc n ∸ toℕ (suc t))
            ≡⟨ P.cong suc (lemma₀ n t) ⟩
          suc (n ∸ toℕ (inject₁ t))
            ≡⟨ P.sym (sm∸n n (toℕ (inject₁ t)) (lemma₁ n t)) ⟩
          suc n ∸ toℕ (inject₁ t)
        ∎
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
          open P.≡-Reasoning
          open Sub.Properties (suc n)

          lemma₀ : ∀ n (t : Fin n) → suc n ∸ toℕ (suc t) ≡ n ∸ toℕ (inject₁ t)
          lemma₀ n t rewrite inject₁-lemma t = P.refl

          lemma₁ : ∀ n (t : Fin n) → toℕ (inject₁ t) N.≤ n
          lemma₁ n t rewrite inject₁-lemma t = suc-inj (≤-step (bounded t))

      size-lemma : ∀ {t} (ctd : ⌛ t) → Sub.size (∁ (visited ctd)) ≡ toℕ t
      size-lemma {t} ctd =
        begin
          Sub.size (∁ (visited ctd))      ≡⟨ Sub.∁-size (visited ctd) ⟩
          suc n ∸ Sub.size (visited ctd)  ≡⟨ P.cong₂ _∸_ P.refl (visited-lemma ctd) ⟩
          suc n ∸ (suc n ∸ toℕ t)         ≡⟨ ∸-assoc _ _ (toℕ t) ≤-refl (≤-step (suc-inj (bounded t))) ⟩
          (suc n ∸ suc n) N.+ toℕ t       ≡⟨ P.cong₂ N._+_ (n∸n≡0 (suc n)) P.refl ⟩
          toℕ t
        ∎
        where
          open P.≡-Reasoning

      queue′ : ∀ {t} (ctd : ⌛ t) →
               let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
               SortedVec (Sub.size $ ∁ $ visited ctd)
      queue′ ctd = fromVec $ Sub.toVec $ ∁ $ visited ctd
        where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      queue : ∀ {t} (ctd : ⌛ t) →
              let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
              SortedVec (toℕ t)
      queue {t} ctd = P.subst SortedVec (size-lemma ctd) (queue′ ctd)
        where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      q′→q : ∀ {t} (ctd : ⌛ (suc t)) →
             let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
             ∀ {p} (P : ∀ {n} → SortedVec n → Set p) → P (queue′ ctd) → P (queue ctd)
      q′→q ctd P Pq′ = {!!}
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      head∉visited : {t : Fin n} (ctd : ⌛ (suc t)) →
                     let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
                     head (queue ctd) ∉ visited ctd
      head∉visited ctd q∈vs with queue ctd
      head∉visited ctd q∈vs | q Sorted.∷ qs ⟨ q≼qs ⟩ = q∉q∷qs (S.here qs q≼qs)
        where
          module S = Sorted (estimateOrder $ V.tabulate $ estimate ctd)

          q∉queue′ : ¬ q S.∈ (queue′ ctd)
          q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

          q∉queue : ¬ q S.∈ (queue ctd)
          q∉queue = q′→q ctd (λ qs → ¬ q S.∈ qs) q∉queue′

          q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
          q∉q∷qs = P.subst (λ qs → ¬ q S.∈ qs) {!P.refl!} q∉queue
      -- q ∈ visited ctd
      -- ⟶ q ∉ ∁ (visited ctd)   by Sub.∁-∈
      -- ⟶ q ∉ Sub.toVec (∁ (visited ctd))   by Sub.toVec-∉¹
      -- ⟶ q ∉ fromVec (Sub.toVec (∁ (visited ctd)))   by fromVec-∉¹
      -- ⟶ q ∉ P.subst SortedVec {! eq !} (fromVec (Sub.toVec (∁ (visited ctd))))
