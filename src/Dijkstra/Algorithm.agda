open import Dijkstra.Algebra

module Dijkstra.Algorithm
  {c ℓ} (alg : DijkstraAlgebra c ℓ) where

open import Dijkstra.Algebra.Properties
import Dijkstra.State as State

open import Data.Fin
open import Data.Nat as N
open import Data.Vec
import Data.Vec.Sorted as Sorted

open import Relation.Binary

open DijkstraAlgebra alg
open RequiresDijkstraAlgebra alg
open State (⊲ᴸ-isStrictTotalOrder _≈?_)

module S = DijkstraState

module RequiresSize (n : ℕ) where

  Est = Vec Carrier (N.suc n)

  Queue : Est → Set _
  Queue est = SortedVec (N.suc n)
    where
      open Estimate est
      open Sorted estimate-isStrictTotalOrder

{-
  relax : (est : Est) → Queue est → Est
  relax est queue = {!!}

  step : DijkstraState (N.suc n) → DijkstraState (N.suc n)
  step state with (S.unseen state)
  step state | zero       = state
  step state | suc unseen =
    record
      { estimate = {!!}
      ; unseen   = inject₁ unseen
      ; queue    = {!!}
    }
-}
