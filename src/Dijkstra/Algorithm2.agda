open import Dijkstra.Algebra

open import Data.Nat.Base hiding (_≤_; _⊔_; _+_; _*_)

module Dijkstra.Algorithm2
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Level using (_⊔_)

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
open import Data.Maybe
open import Data.Product using (∃; ∃₂) renaming (_,_ to _,,_)
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Function using (_$_; _∘_)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ≤-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

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

visited : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Subset (suc n)
visited {i = i} init           = ⁅ i ⁆
visited {i = i} (step state q) = ⁅ q ⁆ ∪ visited state

estimate : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Fin (suc n) → Weight
estimate {n = n} {i} {adj} init           j = I[ i , j ]
estimate {n = n} {i} {adj} (step state q) j = r[ j ] + r[ q ] * A[ q , j ]
  where
    A[_,_] : Fin (suc n) → Fin (suc n) → Weight
    A[ i , j ] = Adj.matrix adj [ i , j ]

    r[_] : Fin (suc n) → Weight
    r[ j ] = estimate state j

visited-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
                (Sub.size (visited state)) ≡ suc n ∸ m
visited-lemma {m} {.m} {i} init rewrite sn∸n≡1 m = Sub.size⁅i⁆≡1 i
visited-lemma {m} {n}  {i} (step state q) with visited-lemma state
... | eq = {!eq!}

∸-assoc : ∀ m n o → m ≥ n → n ≥ o → m ∸ (n ∸ o) ≡ (m ∸ n) Data.Nat.Base.+ o
∸-assoc zero .0 .0 z≤n z≤n = P.refl
∸-assoc (suc m) zero .0 z≤n z≤n = cong suc (P.sym {!!})
∸-assoc (suc m) (suc n) zero (s≤s m≥n) z≤n = {!!}
∸-assoc (suc m) (suc n) (suc o) (s≤s m≥n) (s≤s n≥o) = {!∸-assoc (suc m) n o!}

queue : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
        let open Sorted (estimateOrder $ V.tabulate $ estimate state) in
        SortedVec m
queue {m} {n} state = subst SortedVec (P.trans (Sub.∁-size (visited state)) (P.trans (cong₂ _∸_ P.refl (visited-lemma state)) (P.trans (∸-assoc _ _ m {!≤-refl!} {!!}) (cong₂ Data.Nat.Base._+_ (n∸n≡0 n) P.refl)))) queue′
  where
    open Sorted (estimateOrder $ V.tabulate $ estimate state)

    queue′ : SortedVec (Sub.size $ ∁ $ visited state)
    queue′ = fromVec $ Sub.toVec $ ∁ $ visited state

next : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj (suc m) → State i adj m
next state with queue state
next state | q Sorted.∷ qs ⟨ q≼qs ⟩ = step state q
