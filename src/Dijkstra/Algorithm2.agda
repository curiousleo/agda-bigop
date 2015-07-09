open import Dijkstra.Algebra

open import Data.Nat.Base hiding (_≤_; _⊔_; _+_; _*_)

module Dijkstra.Algorithm2
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Level using (_⊔_)

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Data.Fin hiding (_≤_; _+_)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset hiding (_∈_)
import Data.Fin.Subset.Extra as S
open import Data.List.Any using (module Membership)
open import Data.List.Base
open import Data.Matrix
open import Data.Product using () renaming (_,_ to _,,_)
import Data.Vec as V
import Data.List.Sorted as Sorted

open import Function using (_$_)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

I : ∀ {n} → Adj n
I = tabulate (diagonal 0# 1#) ▦[ (λ i → {! lookup∘tabulate i i !}) ]

I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]

mutual
  data State {n} (i : Fin (suc n)) (adj : Adj (suc n)) : Set (ℓ ⊔ c) where
    init : State i adj
    step : (state : State i adj) (q : Fin (suc n)) →
           let open Sorted (estimateOrder (V.tabulate (estimate state))) in
           (elm : q ≼ sorted-queue state)
           → State i adj

  queue : {n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj → Subset (suc n)
  queue {n} {i} init               = ∁ ⁅ i ⁆
  queue {n} {i} (step state q elm) = queue state ∩ ∁ ⁅ q ⁆

  estimate : {n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj → Fin (suc n) → Weight
  estimate {n} {i} {adj} init               j = I[ i , j ]
  estimate {n} {i} {adj} (step state q elm) j = r[ j ] + r[ q ] * A[ q , j ]
    where
      A[_,_] : Fin (suc n) → Fin (suc n) → Weight
      A[ i , j ] = Adj.matrix adj [ i , j ]

      r[_] : Fin (suc n) → Weight
      r[ j ] = estimate state j

  sorted-queue : {n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj) →
                 let open Sorted (estimateOrder $ V.tabulate $ estimate state) in
                 SortedList
  sorted-queue state = fromList (S.toList (queue state))
    where open Sorted (estimateOrder $ V.tabulate $ estimate state)

module Next {n} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj) where

  order : DecTotalOrder _ _ _
  order = estimateOrder $ V.tabulate $ estimate state

  open Sorted order

  contains-head : ∀ {q} (qs : SortedList) (q≼qs : q ≼ qs) → q ∈ q ∷ qs ⟨ q≼qs ⟩
  contains-head = here

  next : State i adj
  next = {!!}
  {- = step state q $ contains-head {S.size (queue state)} (subst ? ? {!qs!}) (subst ? ? {!q≼qs!})
    where
      eq : suc m ≡ S.size (queue state)
      eq = {!!} -}

next : {n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj) → State i adj
next state with sorted-queue state
next state | Sorted.[] = state
next state | q Sorted.∷ qs ⟨ q≼qs ⟩ = step state q q≼qs







-------------

{-
_subset-∈?_ : {n : ℕ} → (x : Fin n) → (xs : Subset n) → Dec (x ∈ xs)
x subset-∈? V.[] = no (λ ())
zero subset-∈? (inside V.∷ ys)  = yes V.here
zero subset-∈? (outside V.∷ ys) = no (λ ())
suc x subset-∈? (y V.∷ ys) with x subset-∈? ys
... | yes x∈ys = yes $ V.there x∈ys
... | no ¬x∈ys = no contradiction
  where
    contradiction : ¬ y V.∷ ys V.[ suc x ]= inside
    contradiction (V.there x∈ys) = ¬x∈ys x∈ys
-}
