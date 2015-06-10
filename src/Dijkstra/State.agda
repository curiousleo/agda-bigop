module Dijkstra.State where

open import Data.Fin
open import Data.Nat.Base
open import Data.List.Base
open import Data.Vec

record DijkstraState (n : ℕ) : Set where
  field
    visited  : List (Fin n)
    queue    : List (Fin n)
    estimate : Vec (Fin n) n
--  paths : {!!}
