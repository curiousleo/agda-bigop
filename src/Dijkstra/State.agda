module Dijkstra.State where

import Data.AVL.Sets as Sets
open import Data.Fin
open import Data.Nat.Base
open import Data.List.Base
open import Data.Vec
open import Relation.Binary

Fin-isStrictTotalOrder : (n : ℕ) → IsStrictTotalOrder _ _
Fin-isStrictTotalOrder n = StrictTotalOrder.isStrictTotalOrder (strictTotalOrder n)
  where
    open import Data.Fin.Properties

record DijkstraState (n : ℕ) : Set where
  open Sets (Fin-isStrictTotalOrder n)
  field
    visited  : ⟨Set⟩
    queue    : ⟨Set⟩
    estimate : Vec (Fin n) n
--  paths : {!!}
