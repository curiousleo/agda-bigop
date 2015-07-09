open import Dijkstra.Algebra

open import Data.Nat.Base hiding (_≤_; _⊔_; _+_; _*_)

module Dijkstra.Algorithm2
    {c ℓ} (n : ℕ) (alg : DijkstraAlgebra c ℓ)
    where

open import Level using (_⊔_)

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Data.Fin hiding (_≤_; _+_)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset
open import Data.List.Any using (module Membership)
open import Data.List.Base
open import Data.Matrix
open import Data.Product using () renaming (_,_ to _,,_)
import Data.Vec as V
import Data.Vec.Sorted as Sorted

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
  data State (i : Fin (suc n)) (adj : Adj (suc n)) : Set (ℓ ⊔ c) where
    init : State i adj
    step : (state : State i adj) (q : Fin (suc n))
           (q-min : ∀ j → {- -} j ∈ queue state → {- -} estimate state q ≤ estimate state j)
           → State i adj

  queue : {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj → Subset (suc n)
  queue {i} init                 = ∁ ⁅ i ⁆
  queue {i} (step state q q-min) = queue state ∩ ∁ ⁅ q ⁆

  estimate : {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj → Fin (suc n) → Weight
  estimate {i} {adj} init                 j = I[ i , j ]
  estimate {i} {adj} (step state q q-min) j = r[ j ] + r[ q ] * A[ q , j ]
    where
      A[_,_] : Fin (suc n) → Fin (suc n) → Weight
      A[ i , j ] = Adj.matrix adj [ i , j ]

      r[_] : Fin (suc n) → Weight
      r[ j ] = estimate state j

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

size : {n : ℕ} → Subset n → ℕ
size V.[]             = 0
size (inside V.∷ xs)  = suc $ size xs
size (outside V.∷ xs) =       size xs

subsetToVec : {n : ℕ} → (sub : Subset n) → V.Vec (Fin n) (size sub)
subsetToVec V.[]              = V.[]
subsetToVec (inside V.∷ sub)  = zero V.∷ V.map inject₁ (subsetToVec sub)
subsetToVec (outside V.∷ sub) =          V.map inject₁ (subsetToVec sub)

sorted-queue : {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj) →
               let order = estimateOrder (V.tabulate (estimate state)) in
               Sorted.SortedVec order (size (queue state))
sorted-queue state = Sorted.fromVec order $ subsetToVec $ queue state
  where
    order : DecTotalOrder _ _ _
    order = estimateOrder $ V.tabulate $ estimate state

module Next {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj) where

  order : DecTotalOrder _ _ _
  order = estimateOrder $ V.tabulate $ estimate state

  open Sorted order hiding (_∈_)
  
  ∈q : ∀ {m} (q : Fin (suc n)) (qs : SortedVec m) (q≼qs : q ≼ qs) (j : Fin (suc n))
       → j ∈ queue state → estimate state q ≤ estimate state j
  ∈q q Sorted.[] q≼qs j j∈queue = {!queue state!}
  ∈q q (y Sorted.∷ qs ⟨ y≼ys ⟩) q≼qs j j∈queue = {!!}

  next : State i adj
  next with size (queue state) | sorted-queue state
  ... | zero  | []              = state
  ... | suc m | q ∷ qs ⟨ q≼qs ⟩ = step state q (∈q q qs q≼qs)

next : {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj) → State i adj
next {i} {adj} state = Next.next state

{-
next {i} {adj} state = step state q q-min
  where
    A[_,_] : Fin (suc n) → Fin (suc n) → Weight
    A[ i , j ] = Adj.matrix adj [ i , j ]

    r[_] : Fin (suc n) → Weight
    r[ j ] = estimate state j

    q : Fin (suc n)
    q = {!!}

    q-min : ∀ j → r[ q ] ≤ r[ j ]
    q-min j = {!!}
-}
