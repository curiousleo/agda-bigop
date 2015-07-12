open import Dijkstra.Algebra

open import Data.Nat.Base hiding (_≤_; _⊔_; _+_; _*_; _≟_)

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
import Data.Vec.Sorted as Sorted hiding (init)

open import Function using (_$_; _∘_; flip)

open import Relation.Nullary
open import Relation.Unary using (Pred)
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

∸-assoc : ∀ m n o → m ≥ n → n ≥ o → m ∸ (n ∸ o) ≡ (m ∸ n) Data.Nat.Base.+ o
∸-assoc zero .0 .0 z≤n z≤n = P.refl
∸-assoc (suc m) zero .0 z≤n z≤n = P.cong suc (P.sym {!!})
∸-assoc (suc m) (suc n) zero (s≤s m≥n) z≤n = {!!}
∸-assoc (suc m) (suc n) (suc o) (s≤s m≥n) (s≤s n≥o) = {!∸-assoc (suc m) n o!}

---

data State {n} (i : Fin (suc n)) (adj : Adj (suc n)) : ℕ → Set (ℓ ⊔ c) where
  init : State i adj n
  step : {m : ℕ} (prev : State i adj (suc m)) → State i adj m

estimate : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Fin (suc n) → Weight
visited : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Subset (suc n)
visited-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
                (Sub.size (visited state)) ≡ suc n ∸ m

queue : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
        let open Sorted (estimateOrder $ V.tabulate $ estimate state) in
        SortedVec m
queue {m} {n} state = P.subst SortedVec (P.trans (Sub.∁-size (visited state)) (P.trans (P.cong₂ _∸_ P.refl (visited-lemma state)) (P.trans (∸-assoc _ _ m {!≤-refl!} {!!}) (P.cong₂ Data.Nat.Base._+_ (n∸n≡0 n) P.refl)))) queue′
  where
    open Sorted (estimateOrder $ V.tabulate $ estimate state)

    queue′ : SortedVec (Sub.size $ ∁ $ visited state)
    queue′ = fromVec $ Sub.toVec $ ∁ $ visited state

visited {i = i} init         = ⁅ i ⁆
visited {i = i} (step state) = ⁅ head (queue state) ⁆ ∪ visited state
  where open Sorted (estimateOrder $ V.tabulate $ estimate state)

module Abbreviations
    {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m)
    where

  A[_,_] : Fin (suc n) → Fin (suc n) → Weight
  A[ i , j ] = Adj.matrix adj [ i , j ]

  r[_] : Fin (suc n) → Weight
  r[ j ] = estimate state j

estimate {i = i} {adj} init         j = A[ i , j ]
  where
    open Abbreviations (init {i = i} {adj})
estimate {i = i} (step state) j = r[ j ] + r[ q ] * A[ q , j ]
  where
    open Abbreviations state
    open Sorted (estimateOrder $ V.tabulate $ estimate state)
    q = head (queue state)

visited-lemma {m} {.m} {i} init rewrite sn∸n≡1 m = Sub.size⁅i⁆≡1 i
visited-lemma {m} {n}  {i} (step state) = {!!}

iter : ∀ {a} (A : ℕ → Set a) (f : {n : ℕ} → A (suc n) → A n) {n : ℕ} → A n → A zero
iter A f {zero}  x = x
iter A f {suc n} x = f (iter (A ∘ suc) f x)

run : {n : ℕ} (i : Fin (suc n)) (adj : Adj (suc n)) → State i adj 0
run i adj = iter (State i adj) step init

allFin = V.toList ∘ V.allFin

RLS : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → Pred (State i adj m) _
RLS {i = i} state = let open Abbreviations state in
  ∀ j → r[ j ] ≈ I[ i , j ] + (⨁[ q ← Sub.toList (visited state) ] (r[ j ] + r[ q ] * A[ q , j ]))

init‿A≈I+A : {n : ℕ} (i j : Fin (suc n)) {adj : Adj (suc n)} →
             let open Abbreviations (init {n} {i} {adj})
             in A[ i , j ] ≈ I[ i , j ] + A[ i , j ]
init‿A≈I+A i j {adj} with i ≟ j
... | yes i≡j rewrite i≡j =
  begin
    A[ j , j ]               ≡⟨ Adj.diag adj j ⟩
    1#                       ≈⟨ sym (+-idempotent _) ⟩
    1#         + 1#          ≡⟨ P.sym (P.cong₂ _+_ (Adj.diag I j) (Adj.diag adj j)) ⟩
    I[ j , j ] + A[ j , j ]
  ∎
  where open Abbreviations (init {i = i} {adj})
... | no ¬i≡j =
  begin
    A[ i , j ]               ≈⟨ sym (proj₁ +-identity _) ⟩
    0#         + A[ i , j ]  ≡⟨ P.cong₂ _+_ {!!} P.refl ⟩
    I[ i , j ] + A[ i , j ]
  ∎
  where open Abbreviations (init {i = i} {adj})

correct-init : {n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} →
               RLS (init {n} {i} {adj})
correct-init {i = i} {adj} j = trans (init‿A≈I+A i j {adj}) (+-cong refl lemma)
  where
    open Abbreviations (init {i = i} {adj})
    lemma =
      begin
        A[ i , j ]
          ≈⟨ sym (+-idempotent _) ⟩
        A[ i , j ] + A[ i , j ]
          ≈⟨ +-cong refl (sym (*-identityˡ _)) ⟩
        A[ i , j ] + 1# * A[ i , j ]
          ≈⟨ +-cong refl (*-cong (sym (reflexive (Adj.diag adj i))) refl) ⟩
        A[ i , j ] + A[ i , i ] * A[ i , j ]
          ≈⟨ sym (proj₂ +-identity _) ⟩
        (r[ j ] + r[ i ] * A[ i , j ]) + 0#
          ≡⟨⟩
        ⨁[ q ← i ∷ [] ] (r[ j ] + r[ q ] * A[ q , j ])
          ≡⟨ P.cong (⨁-syntax _) (P.sym (Sub.toList⁅i⁆ i)) ⟩
        ⨁[ q ← Sub.toList ⁅ i ⁆ ] (r[ j ] + r[ q ] * A[ q , j ])
      ∎

correct-step : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)}
               (state : State i adj (suc m)) → RLS state → RLS (step state)
correct-step {i = i} state rls j =
  begin
    r[ j ] + r[ q ] * A[ q , j ]
      ≈⟨ +-cong (rls j) (*-cong (reflexive eq) refl) ⟩
    (I[ i , j ] + (⨁[ q ← qs ] (r[ j ] + r[ q ] * A[ q , j ]))) + r′[ q ] * A[ q , j ]
      ≈⟨ {!!} ⟩
    (I[ i , j ] + (⨁[ q ← qs ] (r′[ j ] + r′[ q ] * A[ q , j ]))) + r′[ q ] * A[ q , j ]
      ≈⟨ {!!} ⟩
    I[ i , j ] + (r′[ j ] + ((⨁[ q ← qs ] (r′[ q ] * A[ q , j ])) + r′[ q ] * A[ q , j ]))
      ≈⟨ {!!} ⟩
    I[ i , j ] + (r′[ j ] + (⨁[ q ← qs ∷ʳ q ] (r′[ q ] * A[ q , j ])))
      ≈⟨ {!!} ⟩
    I[ i , j ] + (r′[ j ] + (⨁[ q ← qs′ ] (r′[ q ] * A[ q , j ])))
      ≈⟨ {!!} ⟩
    I[ i , j ] + (⨁[ q ← qs′ ] (r′[ j ] + r′[ q ] * A[ q , j ]))
  ∎
  where
    open Sorted (estimateOrder $ V.tabulate $ estimate state)
    open Abbreviations state
    open Abbreviations (step state) using () renaming (r[_] to r′[_])
    q = head (queue state)
    qs = Sub.toList (visited state)
    qs′ = Sub.toList (⁅ q ⁆ ∪ visited state)

    eq : r[ q ] ≡ r′[ q ]
    eq = {!!}

    eq′ : ∀ j → j ∈ queue state → r[ j ] ≡ r′[ j ]
    eq′ j j∈queue = {!!}
