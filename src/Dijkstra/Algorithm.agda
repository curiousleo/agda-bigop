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

open import Data.Fin.Properties using (_≟_; bounded)
open import Data.List hiding (take; drop)
open import Data.Nat.Properties using (n∸m≤n)
open import Data.Nat.Properties.Extra
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to _,′_)
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

I : ∀ {n} → Fin n → Fin n → Weight
I = diagonal 0# 1#

{-
I : ∀ {n} → Fin n → Fin n → Weight
I i j with i ≟ j
... | yes i≡j = 1#
... | no ¬i≡j = 0#
-}

record Path {n} (i j : Fin n) : Set ℓ where
  constructor via
  field
    mids : List (Fin n)

  edges : List (Fin n × Fin n)
  edges = zip (i ∷ mids) (mids ∷ʳ j)

  weights : (Adj n) → List Weight
  weights adj = map (λ e → adj [ proj₁ e , proj₂ e ]) edges

weightᴸ : ∀ {n} i j → Adj n → Path {n} i j → Weight
weightᴸ i j adj (via [])      = adj [ i , j ]
weightᴸ i j adj (via (q ∷ p)) = adj [ i , q ] * weightᴸ q j adj (via p)

_over_ : ∀ {n i j} → (k : Fin n) → Path {n} i j → Path {n} i k
u over (via v) = via (v ∷ʳ u)

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

    convert : SortedVec size → SortedVec (seen N+ suc (toℕ unseen))
    convert = P.subst SortedVec s≡u+v

  queue : SortedVec (suc (toℕ unseen))
  queue = drop seen (convert vertices)

  visited : SortedVec seen
  visited = take seen (convert vertices)

module InvariantDef
       {n} {adj : Adj (suc n)} {source unseen : Fin (suc n)}
       (state : State adj source unseen) where

  open State state hiding (estimateᴸ)
  open Sorted orderᴸ public
  
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

Invariant : ∀ {n} → {adj : Adj (suc n)} {source unseen : Fin (suc n)} →
            Pred (State adj source unseen) _
Invariant {n} {adj} {source} {unseen} state = ∀ i j → estimateᴸ i j ≈ localSolutionᴸ i j
  where
    open InvariantDef state


initial : ∀ {n} (adj : Adj (suc n)) → (source : Fin (suc n)) →
          Σ (State adj source (fromℕ n)) Invariant
initial {n} adj source = state ,′ invariant
  where
    start : (i j : Fin (suc n)) → Path i j
    start i j = via []

    state : State adj source (fromℕ n)
    state = now start

    open State state hiding (estimateᴸ)
    open InvariantDef state

    qs : List (Fin seen)
    qs = toList (allFin seen)

    inj : Fin _ → Fin _
    inj = flip inject≤ (n∸m≤n (suc (toℕ (fromℕ n))) size)

    invariant : Invariant state
    invariant i j = {!!}
    {- with i ≟ j
    ... | yes i≡j rewrite i≡j = ?
      begin
        adj [ nth i visited , nth j visited ]
          ≈⟨ {!!} ⟩
        (⨁[ q ← qs ] adj [ inj q , inj j ] * adj [ nth i visited , nth  q visited ]) + 1#
      ∎
    ... | no ¬i≡j = ?
      begin
        adj [ nth i visited , nth j visited ]
          ≈⟨ {!!} ⟩
        (⨁[ q ← qs ] adj [ inj q , inj j ] * adj [ nth i visited , nth  q visited ]) + 0#
      ∎ -}

{-
initial-inv : ∀ {n} (adj : Adj (suc n)) → (source : Fin (suc n)) → Invariant (initial adj source)
initial-inv adj source i j with initial adj source
... | p = ?
-}

step : ∀ {n} (adj : Adj (suc n)) {source} {unseen : Fin n} →
       State adj source (suc unseen) → State adj source (inject₁ unseen)
step {n} adj {source} state = now $ relax (head queue)
  where
    open State state
    open Sorted orderᴸ

    w : ∀ {i j} → Path i j → Weight
    w {i} {j} = weightᴸ i j adj

    relax : Fin size → (i j : Fin size) → Path i j
    relax u i j with w (j over (i ⇝ u)) ≤? w (i ⇝ j)
    ... | yes _ = j over (i ⇝ u)
    ... | no  _ = i ⇝ j

--- XXX : move this to a separate file
module Properties {n} (adj : Adj n) where
  open import Algebra.FunctionProperties _≈_

  weight-sum : Associative _*_ →
               (i j k : Fin n) (p q : List (Fin n)) →
               weightᴸ i j adj (via p) * weightᴸ j k adj (via q) ≈
               weightᴸ i k adj (via $ p ++ (j ∷ q))
  weight-sum *-assoc i j k []      q = refl
  weight-sum *-assoc i j k (l ∷ p) q =
    begin
      (adj [ i , l ] * weightᴸ l j adj (via p)) * weightᴸ j k adj (via q)
        ≈⟨ *-assoc _ _ _ ⟩
      adj [ i , l ] * (weightᴸ l j adj (via p) * weightᴸ j k adj (via q))
        ≈⟨ *-cong refl (weight-sum *-assoc l j k p q) ⟩
      adj [ i , l ] * weightᴸ l k adj (via (p ++ j ∷ q))
    ∎
