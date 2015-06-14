open import Dijkstra.Algebra

open import Data.Fin hiding (_+_; _≤_)
open import Data.Matrix using (Matrix; diagonal; tabulate; row; _[_,_])
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
open import Data.Vec using (Vec; allFin; toList)
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

I : ∀ {m n} → Fin m → Fin n → Weight
I = diagonal 0# 1#

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
    _⇝_ : (i j : Fin size) → Path i j

  estimate : Adj size
  estimate = tabulate (λ i j → weight adj (i ⇝ j))

  order : DecTotalOrder _ _ _
  order = estimateOrder (row source estimate)

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
Invariant {n} {adj} {source} {unseen} state = ∀ i j → estimate i j ≡ localSolutionᴿ i j
  where
    open State state hiding (estimate)
    open Sorted order

    estimate : Fin seen → Fin seen → Weight
    estimate i j = weight adj (nth i visited ⇝ nth j visited)

    localSolutionᴿ : Fin seen → Fin seen → Weight
    localSolutionᴿ i j = I i j + ⨁[ q ← qs ] estimate i q * adj [ inj q , inj j ]
      where
        qs = toList (allFin seen)
        inj = flip inject≤ (n∸m≤n (suc (toℕ unseen)) size)

initial : ∀ {n} (adj : Adj (suc n)) → (source : Fin (suc n)) → State adj source (fromℕ n)
initial _ _ = now $ λ i j → path []

step : ∀ {n} (adj : Adj (suc n)) {source} {unseen : Fin n} →
       State adj source (suc unseen) → State adj source (inject₁ unseen)
step {n} adj {source} state = now $ relax (head queue)
  where
    open State state
    open Sorted order

    w : ∀ {i j} → Path i j → Weight
    w = weight adj

    relax : Fin size → (i j : Fin size) → Path i j
    relax u i j with w (j via (i ⇝ u)) ≤? w (i ⇝ j)
    ... | yes _ = j via (i ⇝ u)
    ... | no  _ = i ⇝ j

