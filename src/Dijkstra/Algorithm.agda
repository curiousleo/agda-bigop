open import Dijkstra.Algebra

open import Data.Fin hiding (_+_)
import Data.Matrix as M
open M using (Matrix; diag; _[_,_])
import Data.Nat as N

module Dijkstra.Algorithm
  {c ℓ m} (alg : DijkstraAlgebra c ℓ)
  (Adj : let open DijkstraAlgebra alg in Matrix Carrier (N.suc m) (N.suc m)) where

open import Dijkstra.Algebra.Properties
import Dijkstra.State as State

open import Algebra.FunctionProperties.Core using (Op₂)

open import Data.Fin.Properties hiding (decSetoid)
open N using (ℕ)
open import Data.Vec hiding ([_])
import Data.Vec.Sorted as Sorted
open Sorted using ([]; _∷_⟨_⟩)

open import Function

open import Relation.Nullary
open import Relation.Binary

open DijkstraAlgebra alg
open RequiresDijkstraAlgebra alg
open State (⊲ᴸ-isStrictTotalOrder _≈?_)

module S = DijkstraState

n = N.suc m
Est = Vec Carrier n
Square = Matrix Carrier n n

Queue : Est → Set _
Queue est = SortedVec n
  where
    open EstimateOrder est
    open Sorted isStrictTotalOrder

_⊕_ : Op₂ Square
A ⊕ B = M.tabulate (λ r c → A [ r , c ] + B [ r , c ])

1M : Square
1M = M.tabulate (diag 0# 1#)

sortBy : (est : Est) → (Queue est)
sortBy est = sort (allFin n)
  where
    open EstimateOrder est
    open Sorted isStrictTotalOrder

initial : Fin n → DijkstraState n
initial i =
  record
    { estimate = estimate
    ; unseen   = fromℕ m
    ; queue    = sortBy estimate
    }
  where
    estimate = tabulate (λ j → 1M [ i , j ] + Adj [ i , j ])

infix 7 _[_]

_[_] : ∀ {a n} {A : Set a} → Vec A n → Fin n → A
_[_] = flip lookup

relax : (est : Est) → Queue est → Est
relax est (u ∷ queue ⟨ prf ⟩) = tabulate chill
  where
    chill : Fin n → Carrier
    chill j = est [ j ] + est [ u ] * Adj [ u , j ]

step : DijkstraState n → DijkstraState n
step state with (S.unseen state)
step state | zero       = state
step state | suc unseen =
  record
    { estimate = estimate′
    ; unseen   = inject₁ unseen
    ; queue    = sortBy estimate′
    }
  where
    open DijkstraState state hiding (unseen)
    estimate′ = relax estimate queue
