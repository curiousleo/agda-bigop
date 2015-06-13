open import Dijkstra.Algebra

open import Data.Fin hiding (_+_; _≤_)
open import Data.Matrix using (Matrix; diagonal; _[_,_])
open import Data.Nat.Base
  using (ℕ; zero; suc; _∸_; _≤_; s≤s)
  renaming (_+_ to _N+_)

module Dijkstra.Algorithm
  {c ℓ} (alg : DijkstraAlgebra c ℓ)
  where

open import Dijkstra.Algebra.Properties

open import Algebra.FunctionProperties.Core using (Op₂)

open import Data.Fin.Properties using (bounded)
open import Data.List hiding (drop)
open import Data.Nat.Properties.Extra
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using (Vec; allFin; tabulate)
import Data.Vec.Sorted as Sorted

open import Function

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

Adj : ℕ → _
Adj n = Matrix Weight n n

record Path {n} (i j : Fin n) : Set ℓ where
  constructor path
  field
    mids : List (Fin n)

  edges : List (Fin n × Fin n)
  edges = zip (i ∷ mids) (mids ∷ʳ j)

weight : ∀ {n i j} → Path {n} i j → _ → Weight
weight p adj = foldl _*_ 1# weights
  where
    weights : List Weight
    weights = map (λ e → adj [ proj₁ e , proj₂ e ]) (Path.edges p)

open import Level using (_⊔_)

record State {n} (adj : Adj (suc n)) : Set (c ⊔ ℓ) where

  size : ℕ
  size = suc n

  field
    source : Fin size
    unseen : Fin size
    paths  : (j : Fin size) → Path source j

  estimate : Vec Weight size
  estimate = tabulate (λ (j : Fin size) → weight (paths j) adj)

  order : DecTotalOrder _ _ _
  order = estimateOrder estimate

  open Sorted order

  vertices : SortedVec size
  vertices = fromVec (allFin size)

  private
    visited : ℕ
    visited = size ∸ suc (toℕ unseen)

    -- XXX: The following three definitions should not be necessary and make
    -- type-checking this file terribly slow. Unfortunately I haven't found a nicer
    -- way of convincing Agdaa to type-check "queue" yet.
    s≡u+v : size ≡ visited N+ suc (toℕ unseen)
    s≡u+v = P.sym (∸‿+‿lemma (bounded unseen))

    queue-type : SortedVec size ≡ SortedVec (visited N+ suc (toℕ unseen))
    queue-type = P.cong SortedVec s≡u+v

    convert : SortedVec size → SortedVec (visited N+ suc (toℕ unseen))
    convert xs rewrite queue-type = xs

  queue : SortedVec (suc (toℕ unseen))
  queue = drop visited (convert vertices)

initial : ∀ {n} (adj : Adj (suc n)) → Fin (suc n) → State adj
initial {n} adj source =
  record
    { source = source
    ; unseen = fromℕ n
    ; paths  = λ j → record { mids = [] }
    }

step : ∀ {n} (adj : Adj (suc n)) → State adj → State adj
step {n} adj state with State.unseen state
... | zero       = state
... | suc unseen =
  record
    { source = source
    ; unseen = inject₁ unseen
    ; paths  = relax (head queue)
    }
  where
    open State state hiding (unseen)
    open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_)
    open Sorted order
    open Path

    w : ∀ {j} → Path source j → Weight
    w p = weight {size} {source} p adj

    relax : Fin size → ((j : Fin size) → Path source j)
    relax u j with w {j} (path (mids (paths u) ∷ʳ j)) ≤? w (paths j)
    ... | yes _ = path (mids (paths u) ∷ʳ j)
    ... | no  _ = paths j
