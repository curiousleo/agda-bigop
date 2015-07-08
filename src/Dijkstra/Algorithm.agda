open import Dijkstra.Algebra

open import Data.Fin hiding (_+_; _≤_)
open import Data.Fin.Properties using (_≟_)
open import Data.Matrix using (Matrix; diagonal; tabulate; row; _[_,_]; lookup∘tabulate)
open import Data.Nat.Base
  using (ℕ; zero; suc; _∸_; _≤_; z≤n; s≤s)
  renaming (_+_ to _N+_)

module Dijkstra.Algorithm
  {c ℓ} (alg : DijkstraAlgebra c ℓ)
  where

open import Bigop.Core

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Algebra.FunctionProperties.Core using (Op₂)

open import Data.Empty using (⊥-elim)
open import Data.Fin.Properties using (bounded; to-from)
open import Data.List hiding (take; drop)
open import Data.List.Any
open import Data.Nat.Properties using (n∸m≤n; n∸n≡0)
open import Data.Nat.Properties.Extra
open import Data.Product using (_×_; proj₁; proj₂)
import Data.Vec as V
open V using (Vec; allFin; toList; _[_]≔_)
import Data.Vec.Properties as VP
import Data.Vec.Sorted as Sorted

open import Function

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)
open P.≡-Reasoning renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open Fold +-monoid using (⨁-syntax)
open EqR setoid
import Bigop.Properties.CommutativeMonoid as P
module Σ = P.RequiresCommutativeMonoid +-commutativeMonoid

I : ∀ {n} → Adj n
I = tabulate (diagonal 0# 1#) ▦[ (λ i → {! lookup∘tabulate i i !}) ]

I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]

I-diag-neq : ∀ {n r c} → r ≢ c → I[ r , c ] ≡ 0#
I-diag-neq {n} {r} {c} ¬eq with r ≟ c
I-diag-neq {n} {r} {c} ¬eq | yes eq = ⊥-elim (¬eq eq)
I-diag-neq {n} {r} {c} ¬eq | no  _  = start
  Adj.matrix (I {n}) [ r , c ]  ≣⟨ lookup∘tabulate r c ⟩
  diagonal 0# 1# r c            ≣⟨ diag-lemma r c ¬eq ⟩
  0#                            □
  where
    suc-¬-lemma : ∀ {n} {r c : Fin n} → ¬ suc r ≡ suc c → ¬ r ≡ c
    suc-¬-lemma {r} ¬eq P.refl = ¬eq P.refl

    diag-lemma : ∀ {n} (r c : Fin n) → ¬ r ≡ c → diagonal 0# 1# r c ≡ 0#
    diag-lemma zero    zero    ¬eq = ⊥-elim (¬eq P.refl)
    diag-lemma zero    (suc _) _   = P.refl
    diag-lemma (suc r) zero    ¬eq = P.refl
    diag-lemma (suc r) (suc c) ¬eq = diag-lemma r c (suc-¬-lemma ¬eq)

record State
    {n : ℕ} (adj : Adj (suc n)) (source unseen : Fin (suc n)) : Set c
    where

  constructor now

  size : ℕ
  size = suc n

  field
    estimate : Vec Weight size

  open Sorted (estimateOrder estimate) public

  vertices : SortedVec size
  vertices = fromVec (allFin size)

  seen : ℕ
  seen = size ∸ suc (toℕ unseen)

{-
  private
    -- XXX: The following three definitions should not be necessary and make
    -- type-checking this file terribly slow. Unfortunately I haven't found a nicer
    -- way of convincing Agda to type-check "queue" yet.

    s≡u+v : size ≡ seen N+ suc (toℕ unseen)
    s≡u+v = P.sym (∸‿+‿lemma (bounded unseen))

    queue-type : SortedVec size ≡ SortedVec (seen N+ suc (toℕ unseen))
    queue-type = P.cong SortedVec s≡u+v

    convert : SortedVec size → SortedVec (seen N+ suc (toℕ unseen))
    convert xs = {!!} -- rewrite queue-type = xs
-}

  queue : SortedVec (suc (toℕ unseen))
  queue = drop seen {!!} -- (convert vertices)

  visited : SortedVec seen
  visited = take seen {!!} -- (convert vertices)
  
  A[_,_] : Fin size → Fin size → Weight
  A[ i , j ] = Adj.matrix adj [ i , j ]

  r[_] : Fin size → Weight
  r[ j ] = V.lookup j estimate

  s : List (Fin size)
  s = toList (toVec visited)

initial : ∀ {n} (adj : Adj (suc n)) source → State adj source (fromℕ n)
initial adj source = now $ V.tabulate (const 0#) [ source ]≔ 1#

Invariant : ∀ {n} {adj : Adj (suc n)} {source seen} → Pred (State adj source seen) ℓ
Invariant {n} {adj} {i} {seen} state = ∀ j → r[ j ] ≈ I[ i , j ] + ⨁[ q ← s ] (r[ q ] * A[ q , j ])
  where
    open State state

initial-lemma-eq : ∀ {n} (adj : Adj (suc n)) source → V.lookup source (State.estimate (initial adj source)) ≡ 1#
initial-lemma-eq adj i = VP.lookup∘update i (V.tabulate (const 0#)) 1#

initial-lemma-neq : ∀ {n} (adj : Adj (suc n)) {source j} → j ≢ source → V.lookup j (State.estimate (initial adj source)) ≡ 0#
initial-lemma-neq adj {i} {j} j≠i = start
  V.lookup j (V.tabulate (const 0#) [ i ]≔ 1#)  ≣⟨ VP.lookup∘update′ j≠i (V.tabulate (const 0#)) 1# ⟩
  V.lookup j (V.tabulate (const 0#))            ≣⟨ VP.lookup∘tabulate (const 0#) j ⟩
  0#                                            □

initial-s-empty : ∀ {n} (adj : Adj (suc n)) source → State.s (initial adj source) ≡ []
initial-s-empty {n} adj i = take-zero _ seen=0
  where
    open State (initial adj i)

    seen=0 : seen ≡ 0
    seen=0 =
      start
        n ∸ toℕ (fromℕ n)  ≣⟨ P.cong₂ _∸_ P.refl (to-from n) ⟩
        n ∸ n              ≣⟨ n∸n≡0 n ⟩
        0
      □

    take-zero : ∀ {m n} xs → m ≡ 0 → toList (toVec (take m {n} xs)) ≡ []
    take-zero xs P.refl = P.refl

initial-Invariant : ∀ {n} (adj : Adj (suc n)) source → Invariant (initial adj source)
initial-Invariant adj i j with j ≟ i
... | yes j=i rewrite j=i =
  begin
    V.lookup i (V.tabulate (const 0#) [ i ]≔ 1#)     ≡⟨ initial-lemma-eq adj i ⟩
    1#                                               ≈⟨ sym $ proj₁ +-zero _ ⟩ -- alternatively using +-identity as below
    1#         + ⨁[ q ← s  ] (r[ q ] * A[ q , i ])  ≡⟨ P.cong₂ _+_ (P.sym (Adj.diag I i)) P.refl ⟩
    I[ i , i ] + ⨁[ q ← s  ] (r[ q ] * A[ q , i ])
  ∎
  where
    open State (initial adj i)
... | no  j≠i =
  begin
    V.lookup j (V.tabulate (const 0#) [ i ]≔ 1#)     ≡⟨ initial-lemma-neq adj j≠i ⟩
    0#                                               ≈⟨ sym $ proj₁ +-identity _ ⟩
    0#         + ⨁[ q ← [] ] (r[ q ] * A[ q , j ])  ≡⟨ P.cong₂ _+_ (P.sym (I-diag-neq i≠j)) (P.cong (⨁-syntax (λ q → r[ q ] * A[ q , j ])) (P.sym (initial-s-empty adj i))) ⟩
    I[ i , j ] + ⨁[ q ← s  ] (r[ q ] * A[ q , j ])
  ∎
  where
    open State (initial adj i)
    i≠j : i ≢ j
    i≠j i=j = j≠i (P.sym i=j)

relax : ∀ {n} {adj : Adj (suc n)} {source unseen} (state : State adj source unseen) → Fin (suc n) → Vec Weight (suc n)
relax state q = V.tabulate (λ j → r[ j ] + r[ q ] * A[ q , j ])
  where
    open State state

step : ∀ {n} {adj : Adj (suc n)} {source} {unseen : Fin n} →
       State adj source (suc unseen) → State adj source (inject₁ unseen)
step state = now $ relax state (head queue)
  where
    open State state

module Lemmas {n} {adj : Adj (suc n)} {source unseen}
              (state : State adj source (suc unseen)) where

  open State state hiding (A[_,_])
  open State (step state)
    using ()
    renaming
      ( r[_] to r′[_]
      ; estimate to estimate′
      ; s to s′
      ; queue to queue′
      ; head to head′
      )

  lemma₁ : ∀ q → (P.setoid (Fin size) Membership.∈ q) s → r[ q ] ≡ r′[ q ]
  lemma₁ q q∈s = {!!}

  lemma₂ : r[ head queue ] ≡ r′[ head queue ]
  lemma₂ = {!!}

  lemma₃ : s ∷ʳ head queue ≡ s′
  lemma₃ = {!!}

step-Invariant : ∀ {n} {adj : Adj (suc n)} {source unseen} →
                 (state : State adj source (suc unseen)) →
                 Invariant state → Invariant (step state)
step-Invariant {adj = adj} {i} state invariant j =
  begin
    V.lookup j (relax state (head queue))
      ≡⟨ VP.lookup∘tabulate (λ j → r[ j ] + (r[ head queue ] * A[ head queue , j ])) j ⟩
    r[ j ] + r[ head queue ] * A[ head queue , j ]
      ≈⟨ +-cong (invariant j) refl ⟩
    (I[ i , j ] + ⨁[ q ← s ] (r[ q ] * A[ q , j ])) + r[ head queue ] * A[ head queue , j ]
      ≈⟨ +-assoc _ _ _ ⟩
    I[ i , j ] + (⨁[ q ← s ] (r[ q ] * A[ q , j ]) + r[ head queue ] * A[ head queue , j ])
      ≈⟨ +-cong refl (+-cong (Σ.cong′ s P.refl (λ q q∈s → *-cong (reflexive (lemma₁ q q∈s)) refl)) (*-cong (reflexive lemma₂) refl)) ⟩
    I[ i , j ] + (⨁[ q ← s ] (r′[ q ] * A[ q , j ]) + r′[ head queue ] * A[ head queue , j ])
      ≈⟨ +-cong refl (sym (Σ.snoc (λ q → r′[ q ] * A[ q , j ]) (head queue) s)) ⟩
    I[ i , j ] + ⨁[ q ← s ∷ʳ head queue ] (r′[ q ] * A[ q , j ])
      ≡⟨ P.cong₂ _+_ P.refl (P.cong (⨁-syntax (λ q → r′[ q ] * A[ q , j ])) lemma₃) ⟩
    I[ i , j ] + ⨁[ q ← s′ ] (r′[ q ] * A[ q , j ])
  ∎
  where
    open State state hiding (A[_,_])
    open State (step state)
      using ()
      renaming
        ( r[_] to r′[_]
        ; estimate to estimate′
        ; s to s′
        ; queue to queue′
        ; head to head′
        )

    open Lemmas state
        
    A[_,_] : Fin size → Fin size → Weight
    A[ i , j ] = Adj.matrix adj [ i , j ]
