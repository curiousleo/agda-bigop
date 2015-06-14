open import Dijkstra.Algebra

open import Data.Fin hiding (_+_; _≤_)
open import Data.Matrix using (Matrix; diagonal; _[_,_])
open import Data.Nat.Base
  using (ℕ; zero; suc; _∸_; _≤_; s≤s)
  renaming (_+_ to _N+_)

module Dijkstra.Algorithm
  {c ℓ} (alg : DijkstraAlgebra c ℓ)
  where

open import Bigop.Core

open import Dijkstra.Algebra.Properties

open import Algebra.FunctionProperties.Core using (Op₂)

open import Data.Fin.Properties using (bounded)
open import Data.List hiding (take; drop)
open import Data.Nat.Properties using (n∸m≤n)
open import Data.Nat.Properties.Extra
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using (Vec; allFin; tabulate; toList)
import Data.Vec.Sorted as Sorted

open import Function

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open Fold +-monoid using (⨁-syntax)

Adj : ℕ → _
Adj n = Matrix Weight n n

record Path {n} (i j : Fin n) : Set ℓ where
  constructor path
  field
    mids : List (Fin n)

  edges : List (Fin n × Fin n)
  edges = zip (i ∷ mids) (mids ∷ʳ j)

weight : ∀ {n i j} → Adj n → Path {n} i j → Weight
weight adj p = foldl _*_ 1# weights
  where
    weights : List Weight
    weights = map (λ e → adj [ proj₁ e , proj₂ e ]) (Path.edges p)

_via_ : ∀ {n i j} → (k : Fin n) → Path {n} i j → Path {n} i k
u via (path v) = path (v ∷ʳ u)

open import Level using (_⊔_)

record State {n} (adj : Adj (suc n))
             (source unseen : Fin (suc n)) : Set (c ⊔ ℓ) where

  constructor now

  size : ℕ
  size = suc n

  field
    ⇝ : (j : Fin size) → Path source j

  estimate : Vec Weight size
  estimate = tabulate (λ (j : Fin size) → weight adj (⇝ j))

  order : DecTotalOrder _ _ _
  order = estimateOrder estimate

  open Sorted order

  vertices : SortedVec size
  vertices = fromVec (allFin size)

  seen : ℕ
  seen = size ∸ suc (toℕ unseen)

  private
    -- XXX: The following three definitions should not be necessary and make
    -- type-checking this file terribly slow. Unfortunately I haven't found a nicer
    -- way of convincing Agdaa to type-check "queue" yet.
    s≡u+v : size ≡ seen N+ suc (toℕ unseen)
    s≡u+v = P.sym (∸‿+‿lemma (bounded unseen))

    queue-type : SortedVec size ≡ SortedVec (seen N+ suc (toℕ unseen))
    queue-type = P.cong SortedVec s≡u+v

    convert : SortedVec size → SortedVec (seen N+ suc (toℕ unseen))
    convert xs rewrite queue-type = xs

  queue : SortedVec (suc (toℕ unseen))
  queue = drop seen (convert vertices)

  visited : SortedVec seen
  visited = take seen (convert vertices)

Invariant : ∀ {n} → {adj : Adj (suc n)} {source unseen : Fin (suc n)} →
            Pred (State adj source unseen) _
Invariant {n} {adj} {source} {unseen} state = ∀ j → weightTo j ≡ localSolutionᴿ j
  where
    open State state
    open Sorted order

    weightTo : Fin seen → Weight
    weightTo j = weight adj (⇝ (nth j visited))

    localSolutionᴿ : Fin seen → Weight
    localSolutionᴿ j = I + ⨁[ i ← is ] weightTo i * adj [ inj i , inj j ]
      where
        I = diagonal 0# 1# source j
        is = toList (allFin seen)
        inj = flip inject≤ (n∸m≤n (suc (toℕ unseen)) size)

initial : ∀ {n} (adj : Adj (suc n)) → (source : Fin (suc n)) → State adj source (fromℕ n)
initial _ _ = now $ λ j → path []

step : ∀ {n} (adj : Adj (suc n)) {source} {unseen : Fin n} →
       State adj source (suc unseen) → State adj source (inject₁ unseen)
step {n} adj {source} state = now $ relax (head queue)
  where
    open State state
    open Sorted order

    w : ∀ {j} → Path source j → Weight
    w = weight {size} {source} adj

    relax : Fin size → ((j : Fin size) → Path source j)
    relax u j with w (j via (⇝ u)) ≤? w (⇝ j)
    ... | yes _ = j via (⇝ u)
    ... | no  _ = ⇝ j
