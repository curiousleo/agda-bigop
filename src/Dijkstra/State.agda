module Dijkstra.State where

import Dijkstra.PriorityQueue as PQ

open import Data.Fin
open import Data.Nat.Base
open import Data.List.Base
open import Data.Vec
open import Data.Unit
open import Function
open import Relation.Binary

Fin-isStrictTotalOrder : (n : ℕ) → IsStrictTotalOrder _ _
Fin-isStrictTotalOrder n = StrictTotalOrder.isStrictTotalOrder (strictTotalOrder n)
  where
    open import Data.Fin.Properties using (strictTotalOrder)

record DijkstraState (n : ℕ) : Set where
  open PQ (const ⊤) (Fin-isStrictTotalOrder n)
  field
    visited  : PQ
    queue    : PQ
    estimate : Vec (Fin n) n
--  paths : {!!}
