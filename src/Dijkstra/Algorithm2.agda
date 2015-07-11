open import Dijkstra.Algebra

open import Data.Nat.Base hiding (_≤_; _⊔_; _+_; _*_)

module Dijkstra.Algorithm2
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Level using (_⊔_)

open import Bigop.Core

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Data.Fin hiding (_≤_; _+_)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset hiding (_∈_)
import Data.Fin.Subset.Extra as Sub
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Nat.Properties using (n∸n≡0; ≤-step; +-∸-assoc; 0∸n≡0)
open import Data.List.Any using (module Membership)
open import Data.List.Base
open import Data.Matrix
open import Data.Product using (∃; ∃₂; proj₁; proj₂) renaming (_,_ to _,,_)
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Function using (_$_; _∘_; flip)

open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)
import Relation.Binary.EqReasoning as EqR

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ≤-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open EqR setoid
open Fold +-monoid using (⨁-syntax)

I : ∀ {n} → Adj n
I = tabulate (diagonal 0# 1#) ▦[ (λ i → {! lookup∘tabulate i i !}) ]

I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]

sn∸n≡1 : ∀ n → suc n ∸ n ≡ 1
sn∸n≡1 zero    = P.refl
sn∸n≡1 (suc n) = sn∸n≡1 n

data State {n} (i : Fin (suc n)) (adj : Adj (suc n)) : ℕ → Set (ℓ ⊔ c) where
  init : State i adj n
  step : {m : ℕ} (prev : State i adj (suc m)) (q : Fin (suc n)) → State i adj m

chosen : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) → Fin (suc n)
chosen {i = i} init           = i
chosen         (step state q) = q

visited : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Subset (suc n)
visited {i = i} init           = ⁅ i ⁆
visited {i = i} (step state q) = ⁅ q ⁆ ∪ visited state

estimate : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Fin (suc n) → Weight

module Abbreviations
    {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m)
    where

  A[_,_] : Fin (suc n) → Fin (suc n) → Weight
  A[ i , j ] = Adj.matrix adj [ i , j ]

  r[_] : Fin (suc n) → Weight
  r[ j ] = estimate state j

estimate {n = n} {i} {adj} init           j = I[ i , j ]
estimate {n = n} {i} {adj} (step state q) j = r[ j ] + r[ q ] * A[ q , j ]
  where open Abbreviations state

visited-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
                (Sub.size (visited state)) ≡ suc n ∸ m
visited-lemma {m} {.m} {i} init rewrite sn∸n≡1 m = Sub.size⁅i⁆≡1 i
visited-lemma {m} {n}  {i} (step state q) with visited-lemma state
... | eq = {!eq!}

∸-assoc : ∀ m n o → m ≥ n → n ≥ o → m ∸ (n ∸ o) ≡ (m ∸ n) Data.Nat.Base.+ o
∸-assoc zero .0 .0 z≤n z≤n = P.refl
∸-assoc (suc m) zero .0 z≤n z≤n = P.cong suc (P.sym {!!})
∸-assoc (suc m) (suc n) zero (s≤s m≥n) z≤n = {!!}
∸-assoc (suc m) (suc n) (suc o) (s≤s m≥n) (s≤s n≥o) = {!∸-assoc (suc m) n o!}

queue : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
        let open Sorted (estimateOrder $ V.tabulate $ estimate state) in
        SortedVec m
queue {m} {n} state = P.subst SortedVec (P.trans (Sub.∁-size (visited state)) (P.trans (P.cong₂ _∸_ P.refl (visited-lemma state)) (P.trans (∸-assoc _ _ m {!≤-refl!} {!!}) (P.cong₂ Data.Nat.Base._+_ (n∸n≡0 n) P.refl)))) queue′
  where
    open Sorted (estimateOrder $ V.tabulate $ estimate state)

    queue′ : SortedVec (Sub.size $ ∁ $ visited state)
    queue′ = fromVec $ Sub.toVec $ ∁ $ visited state

next : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj (suc m) → State i adj m
next state with queue state
next state | q Sorted.∷ qs ⟨ q≼qs ⟩ = step state q

iter : ∀ {a} (A : ℕ → Set a) (f : {n : ℕ} → A (suc n) → A n) {n : ℕ} → A n → A zero
iter A f {zero}  x = x
iter A f {suc n} x = iter A f (f x)

run : {n : ℕ} (i : Fin (suc n)) (adj : Adj (suc n)) → State i adj 0
run i adj = iter (State i adj) next init

allFin = V.toList ∘ V.allFin

next-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj (suc m)) →
             ∃ λ q → next state ≡ step state q
next-lemma state with next state
next-lemma {zero} {.0} {i} state | init = {!!}
next-lemma {suc m} {.(suc m)} {i} state | init = {!!}
next-lemma {m} {n} {i} state | step state′ q = q ,, (P.cong (flip step q) {!!})

correct-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj (suc m)) → (j : Fin (suc n)) →
                let open Abbreviations state
                    open Abbreviations (next state) using () renaming (r[_] to r′[_])
                    q = chosen (next state)
                in r′[ j ] ≈ r[ j ] + r[ q ] * A[ q , j ]
correct-lemma state j with next state
correct-lemma {zero} {.0} {zero} state zero | init = {!!}
correct-lemma {zero} {.0} {zero} state (suc ()) | init
correct-lemma {zero} {.0} {suc ()} state j | init
correct-lemma {suc m} {.(suc m)} {i} state j | init = {!!}
correct-lemma state j | step state′ q = {!!}
{-
  begin
    r′[ j ]
      ≡⟨⟩
    estimate (next state) j
      ≈⟨ {!r[ q ]!} ⟩
    r[ j ] + r[ q ] * A[ q , j ]
  ∎
  where
    open Abbreviations state
    open Abbreviations (next state) using () renaming (r[_] to r′[_])
    q = chosen (next state)
    -}

correct : {n : ℕ} (i : Fin (suc n)) (adj : Adj (suc n)) (j : Fin (suc n)) →
          let open Abbreviations (run i adj) in
          r[ j ] ≈ I[ i , j ] + (⨁[ q ← allFin (suc n) ] (r[ j ] + r[ q ] * A[ q , j ]))
correct {zero} zero adj zero =
  begin
    r[ j ]                                                            ≡⟨⟩
    1#                                                                ≈⟨ sym (proj₁ +-zero _) ⟩
    1# + (1# + 1# * (A[ zero , zero ]) + 0#)                          ≡⟨⟩
    I[ i , j ] + (⨁[ q ← allFin 1 ] (r[ j ] + r[ q ] * A[ q , j ]))
  ∎
  where
    open Abbreviations (run zero adj)
    i j : Fin 1
    i = zero
    j = zero
correct {zero} zero adj (suc ())
correct {zero} (suc ()) adj j
correct {suc n} i adj j =
  begin
    r[ j ]  ≡⟨⟩
    estimate (iter (State i adj) next (next init)) j
      ≈⟨ {!next init!} ⟩
    I[ i , j ] + (⨁[ q ← allFin (suc (suc n)) ] (r[ j ] + r[ q ] * A[ q , j ]))
  ∎
  where
    open Abbreviations (run i adj)
