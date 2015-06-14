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
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open Fold +-monoid using (⨁-syntax)
open EqR setoid

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

  weights : (Adj n) → List Weight
  weights adj = map (λ e → adj [ proj₁ e , proj₂ e ]) edges

weightᴸ : ∀ {n} i j → Adj n → Path {n} i j → Weight
weightᴸ i j adj (path [])      = adj [ i , j ]
weightᴸ i j adj (path (q ∷ p)) = adj [ i , q ] * weightᴸ q j adj (path p)

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

  estimateᴸ : Adj size
  estimateᴸ = tabulate (λ i j → weightᴸ i j adj (i ⇝ j))

  orderᴸ : DecTotalOrder _ _ _
  orderᴸ = estimateOrder (row source estimateᴸ)

  open Sorted orderᴸ

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
    convert xs = {!!} -- rewrite queue-type = xs

  queue : SortedVec (suc (toℕ unseen))
  queue = drop seen (convert vertices)

  visited : SortedVec seen
  visited = take seen (convert vertices)

Invariant : ∀ {n} → {adj : Adj (suc n)} {source unseen : Fin (suc n)} →
            Pred (State adj source unseen) _
Invariant {n} {adj} {source} {unseen} state = ∀ i j → estimateᴸ i j ≡ localSolutionᴸ i j
  where
    open State state hiding (estimateᴸ)
    open Sorted orderᴸ

    estimateᴸ : Fin seen → Fin seen → Weight
    estimateᴸ i j = weightᴸ _ _ adj (nth i visited ⇝ nth j visited)

    localSolutionᴸ : Fin seen → Fin seen → Weight
    localSolutionᴸ i j = (⨁[ q ← qs ] adj [ inj q , inj j ] * estimateᴸ i q) + I i j
      where
        qs = toList (allFin seen)
        inj = flip inject≤ (n∸m≤n (suc (toℕ unseen)) size)

{-
    localSolutionᴿ : Fin seen → Fin seen → Weight
    localSolutionᴿ i j = I i j + ⨁[ q ← qs ] estimate i q * adj [ inj q , inj j ]
      where
        qs = toList (allFin seen)
        inj = flip inject≤ (n∸m≤n (suc (toℕ unseen)) size)
-}

initial : ∀ {n} (adj : Adj (suc n)) → (source : Fin (suc n)) → State adj source (fromℕ n)
initial _ _ = now $ λ i j → path []

step : ∀ {n} (adj : Adj (suc n)) {source} {unseen : Fin n} →
       State adj source (suc unseen) → State adj source (inject₁ unseen)
step {n} adj {source} state = now $ relax (head queue)
  where
    open State state
    open Sorted orderᴸ

    w : ∀ {i j} → Path i j → Weight
    w {i} {j} = weightᴸ i j adj

    relax : Fin size → (i j : Fin size) → Path i j
    relax u i j with w (j via (i ⇝ u)) ≤? w (i ⇝ j)
    ... | yes _ = j via (i ⇝ u)
    ... | no  _ = i ⇝ j

--- XXX : move this to a separate file
module Properties {n} (adj : Adj n) where
  open import Algebra.FunctionProperties _≈_

  weight-sum : Associative _*_ →
               (i j k : Fin n) (p q : List (Fin n)) →
               weightᴸ i j adj (path p) * weightᴸ j k adj (path q) ≈
               weightᴸ i k adj (path $ p ++ (j ∷ q))
  weight-sum *-assoc i j k []      q = refl
  weight-sum *-assoc i j k (l ∷ p) q =
    begin
      (adj [ i , l ] * weightᴸ l j adj (path p)) * weightᴸ j k adj (path q)
        ≈⟨ *-assoc _ _ _ ⟩
      adj [ i , l ] * (weightᴸ l j adj (path p) * weightᴸ j k adj (path q))
        ≈⟨ *-cong refl (weight-sum *-assoc l j k p q) ⟩
      adj [ i , l ] * weightᴸ l k adj (path (p ++ j ∷ q))
    ∎
