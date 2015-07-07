open import Dijkstra.Algebra

module Dijkstra.Adjacency
       {c ℓ} (alg : DijkstraAlgebra c ℓ)
       where

open import Data.Matrix
open import Data.Nat.Base using (ℕ)

open import Relation.Binary.PropositionalEquality using (_≡_)

open DijkstraAlgebra alg renaming (Carrier to Weight)

record Adj (n : ℕ) : Set c where
  constructor _▦[_]
  field
    matrix : Matrix Weight n n
    diag   : ∀ i → matrix [ i , i ] ≡ 1#
