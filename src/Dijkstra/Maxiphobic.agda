open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Dijkstra.Maxiphobic
  {k ℓ}
  {Key : Set k}
  {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Maybe
open import Data.Product

open IsStrictTotalOrder isStrictTotalOrder

data Tree : Set k where
  null : Tree
  fork : (label : Key) (left : Tree) (right : Tree) → Tree

empty : Tree
empty = null

singleton : Key → Tree
singleton k = fork k null null

minElem : Tree → Maybe Key
minElem null                  = nothing
minElem (fork label _ _) = just label

mutual
  merge : Tree → Tree → Tree
  merge null               u                  = u
  merge t                  null               = t
  merge (fork lₜ tₗ tᵣ) (fork lᵤ uₗ uᵣ) with compare lₜ lᵤ
  ... | tri< a ¬b ¬c = fork lₜ (merge tₗ tᵣ) (merge u (singleton lᵤ))
    where
      u = (fork lᵤ uₗ uᵣ)
  ... | tri≈ ¬a b ¬c = fork lₜ {!!} {!!}
  ... | tri> ¬a ¬b c = {!!}
  -- = fork (sₜ + size u) lₜ tₗ (merge tᵣ u)

  join : Tree → Tree → Tree
  join null u = u
  join (fork label t₁ t₂) u = {!!}

{-
orderBySize : Tree × Tree × Tree → Tree × Tree × Tree
orderBySize (t , u , v) with compare (size t) (size u) | compare (size t) (size v) | compare (size u) (size v)
... | a | b | c = ?
-}
