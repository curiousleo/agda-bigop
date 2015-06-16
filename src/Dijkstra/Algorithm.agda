open import Dijkstra.Algebra

module Dijkstra.Algorithm
  {c ℓ} (alg : DijkstraAlgebra c ℓ)
  where

open import Bigop.Core

open import Dijkstra.Algebra.Properties

open import Algebra.FunctionProperties.Core using (Op₂)

open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_+_; _≤_)
open import Data.Fin.Properties using (_≟_; to-from; bounded; inject₁-lemma)
open import Data.List hiding (take; drop)
import Data.Matrix as M
open M using (Matrix; diagonal; row; _[_,_]; Pointwise)
open import Data.Nat.Base
  using (ℕ; zero; suc; _∸_; s≤s)
  renaming (_+_ to _N+_; _≤_ to _N≤_)
open import Data.Nat.Properties using (≤-step; n∸m≤n; m+n∸n≡m; n∸n≡0; +-∸-assoc)
open import Data.Nat.Properties.Simple using (+-suc) renaming (+-comm to N+-comm)
open import Data.Nat.Properties.Extra
open import Data.Product using (∃; Σ; _×_; proj₁; proj₂) renaming (_,_ to _,′_)
open import Data.Vec using (Vec; allFin; toList; tabulate)
import Data.Vec.Sorted as Sorted

open import Function

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)
open P.≡-Reasoning
  using ()
  renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open Fold +-monoid using (⨁-syntax)
open EqR setoid

Adj : ℕ → _
Adj n = Matrix Weight n n

postulate
  diag-1# : ∀ {n} → (adj : Adj n) → (i : Fin n) → (adj [ i , i ]) ≡ 1#

_⊗_ : ∀ {n} → Adj n → Adj n → Adj n
A ⊗ B = M.tabulate $ λ i j → ⨁[ q ← toList (allFin _) ] A [ i , q ] * B [ q , j ]

_⊕_ : ∀ {n} → Adj n → Adj n → Adj n
A ⊕ B = M.tabulate $ λ i j → A [ i , j ] + B [ i , j ]

I : ∀ {n} → Fin n → Fin n → Weight
I i j with i ≟ j
... | yes i≡j = 1#
... | no ¬i≡j = 0#

ident : ∀ {n} → Adj n
ident = M.tabulate $ λ i j → diagonal 0# 1# i j

infix 4 _≋_

_≋_ : ∀ {n} → Rel (Adj n) ℓ
_≋_ = Pointwise _≈_

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
weightᴸ i j adj (via (q ∷ p)) = (adj [ i , q ]) * weightᴸ q j adj (via p)

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

  estimateᴸ : Fin size → Fin size → Weight
  estimateᴸ i j = weightᴸ i j adj (i ⇝ j)

  orderᴸ : DecTotalOrder _ _ _
  orderᴸ = estimateOrder $ tabulate $ estimateᴸ source

  open Sorted orderᴸ public

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

    convert : SortedVec size → SortedVec (suc seen N+ toℕ unseen)
    convert = P.subst SortedVec (P.trans s≡u+v (+-suc (n ∸ toℕ unseen) (toℕ unseen)))

  queue : SortedVec (toℕ unseen)
  queue = drop (suc seen) (convert vertices)

  visited : SortedVec (suc seen)
  visited = take (suc seen) (convert vertices)

  left : Adj (suc seen)
  left = M.tabulate (λ i j → estimateᴸ (lookup visited i) (lookup visited j))

  adj-visited : Adj (suc seen)
  adj-visited = M.tabulate (λ i j → adj [ lookup visited i , lookup visited j ])  

{-
  localSolutionᴿ : Fin (suc seen) → Fin (suc seen) → Weight
  localSolutionᴿ i j = I i j + ⨁[ q ← qs ] estimate i q * adj [ inj q , inj j ]
    where
      qs = toList (allFin (suc seen))
      inj = flip inject≤ (n∸m≤n (suc (toℕ unseen)) size)
-}

Invariant : ∀ {n} {adj : Adj (suc n)} {source unseen} →
            Pred (State adj source unseen) _
Invariant {n} {adj} {source} {unseen} state = left ≋ (adj-visited ⊗ left) ⊕ ident
  where
    open State state

initial : ∀ {n} (adj : Adj (suc n)) → (source : Fin (suc n)) →
          Σ (State adj source (fromℕ n)) Invariant
initial {n} adj source = state ,′ invariant
  where
    state : State adj source (fromℕ n)
    state = now $ λ i j → via []

    open State state

    seen≡0 : seen ≡ 0
    seen≡0 =
      start
        n ∸ toℕ (fromℕ n)  ≣⟨ P.cong₂ _∸_ P.refl (to-from n) ⟩
        n ∸ n              ≣⟨ n∸n≡0 n ⟩
        0
      □

    seen-lemma : (i : Fin (suc (seen))) → i ≡ zero
    seen-lemma rewrite seen≡0 = Fin1-lemma
      where
        Fin1-lemma : (i : Fin 1) → i ≡ zero
        Fin1-lemma zero = P.refl
        Fin1-lemma (suc ())

    invariant : (i j : Fin (suc seen)) → left [ i , j ] ≈ ((adj-visited ⊗ left) ⊕ ident) [ i , j ]
    invariant i j =
      begin
        left [ i , j ]
          ≡⟨ P.cong₂ (_[_,_] left) (seen-lemma i) (seen-lemma j) ⟩
        left [ zero , zero ]
          ≡⟨ diag-1# left zero ⟩
        1#
          ≡⟨ P.sym $ diag-1# ((adj-visited ⊗ left) ⊕ ident) zero ⟩
        ((adj-visited ⊗ left) ⊕ ident) [ zero , zero ]
          ≡⟨ P.sym $ P.cong₂ (_[_,_] ((adj-visited ⊗ left) ⊕ ident)) (seen-lemma i) (seen-lemma j) ⟩
        ((adj-visited ⊗ left) ⊕ ident) [ i , j ]
      ∎

step : ∀ {n} (adj : Adj (suc n)) {source} {unseen : Fin n} →
       State adj source (suc unseen) → State adj source (inject₁ unseen)
step {n} adj {source} state = now $ relax (head queue)
  where
    open State state

    w : ∀ {i j} → Path i j → Weight
    w {i} {j} = weightᴸ i j adj

    relax : Fin size → (i j : Fin size) → Path i j
    relax u i j with w (j over (i ⇝ u)) ≤? w (i ⇝ j)
    ... | yes _ = j over (i ⇝ u)
    ... | no  _ = i ⇝ j

step′ : ∀ {n} (adj : Adj (suc n)) {source} {unseen : Fin n} →
        Σ (State adj source (suc unseen)) Invariant →
        Σ (State adj source (inject₁ unseen)) Invariant
step′ {n} adj {source} {unseen} (state ,′ invariant) = state′ ,′ {!invariant-helper!} --invariant′
  where
    state′ = step adj state
    module S = State state
    open State state′

    0<seen : seen ≡ suc S.seen
    0<seen =
      start
        n ∸ toℕ (inject₁ unseen)      ≣⟨ P.cong₂ _∸_ P.refl (inject₁-lemma unseen) ⟩
        (1 N+ n) ∸ (1 N+ toℕ unseen)  ≣⟨ +-∸-assoc 1 (bounded unseen) ⟩
        1 N+ (n ∸ (1 N+ toℕ unseen))
      □

    convert : Fin (suc S.seen) → Fin seen
    convert = P.subst Fin (P.sym 0<seen)

    invariant′ : ∀ i j → estimateᴸ (lookup visited i) (lookup visited j) ≈
                        (⨁[ q ← toList (allFin _) ] adj-visited [ i , q ] * left [ q , j ]) + ident [ i , j ]
    invariant′ i j =
      begin
        estimateᴸ (lookup visited i) (lookup visited j)
          ≈⟨ {!!} ⟩
        (⨁[ q ← toList (allFin _) ] adj-visited [ i , q ] * left [ q , j ]) + ident [ i , j ]
      ∎

    invariant-helper : ∀ i j →
                       estimateᴸ (lookup visited i) (lookup visited j) ≈
                       (⨁[ q ← toList (allFin _) ] adj-visited [ i , q ] * left [ q , j ]) + ident [ i , j ] →
                       left [ i , j ] ≈ ((adj-visited ⊗ left) ⊕ ident) [ i , j ]
    invariant-helper i j eq =
      begin
        left [ i , j ]
          ≡⟨ M.lookup∘tabulate
               {f = λ i j → estimateᴸ (lookup visited i) (lookup visited j)} i j ⟩
        estimateᴸ (lookup visited i) (lookup visited j)
          ≈⟨ eq ⟩
        (⨁[ q ← toList (allFin _) ] adj-visited [ i , q ] * left [ q , j ]) + ident [ i , j ]
          ≈⟨ +-cong (sym (reflexive (M.lookup∘tabulate {f = λ i j → ⨁[ q ← toList (allFin _) ] adj-visited [ i , q ] * left [ q , j ]} i j))) refl ⟩
        (adj-visited ⊗ left) [ i , j ] + ident [ i , j ]
          ≡⟨ P.sym (M.lookup∘tabulate
               {f = λ i j → (adj-visited ⊗ left) [ i , j ] + ident [ i , j ]} i j) ⟩
        ((adj-visited ⊗ left) ⊕ ident) [ i , j ]
      ∎

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
      (((adj [ i , l ]) * weightᴸ l j adj (via p)) * weightᴸ j k adj (via q))
        ≈⟨ *-assoc _ _ _ ⟩
      ((adj [ i , l ]) * (weightᴸ l j adj (via p) * weightᴸ j k adj (via q)))
        ≈⟨ *-cong refl (weight-sum *-assoc l j k p q) ⟩
      ((adj [ i , l ]) * weightᴸ l k adj (via (p ++ j ∷ q)))
    ∎
