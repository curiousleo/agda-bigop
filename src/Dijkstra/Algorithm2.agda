open import Dijkstra.Algebra

module Dijkstra.Algorithm2
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    where

open import Level using (_⊔_)

open import Dijkstra.Adjacency alg
open import Dijkstra.Algebra.Properties

open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_≤_; _+_)
open import Data.Fin.Properties using (_≟_; to-from; inject₁-lemma; bounded)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
import Data.Nat as N
open N using (ℕ; zero; suc; _∸_; z≤n; s≤s)
open import Data.Nat.MoreProperties
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
-- open P.≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
import Relation.Binary.EqReasoning as EqR

open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤?_; _≤_) renaming (refl to ⊴ᴸ-refl)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
-- open EqR setoid
open import Bigop.SubsetCore +-commutativeMonoid

open DecTotalOrder N.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

I : ∀ {n} → Adj n
I = matrix ▦[ diag ]
  where
    matrix : Matrix Weight _ _
    matrix = tabulate (diagonal 0# 1#)

    diag : ∀ i → (matrix [ i , i ]) ≡ 1#
    diag i = P.trans (lookup∘tabulate i i) (diagonal-diag i)

I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]

iter : ∀ {a} (A : ℕ → Set a) (f : {n : ℕ} → A (suc n) → A n) {n : ℕ} → A n → A zero
iter A f {zero}  x = x
iter A f {suc n} x = f (iter (A ∘ suc) f x)

---

module _ {n} (i : Fin (suc n)) (adj : Adj (suc n)) where

  open import Data.Fin.Countdown

  private

    A[_,_] : Fin (suc n) → Fin (suc n) → Weight
    A[ i , j ] = Adj.matrix adj [ i , j ]

    mutual

      estimate : {t : Fin (suc n)} → ⌛ t → Fin (suc n) → Weight
      estimate start        j = A[ i , j ]
      estimate (tick t ctd) j = r j + r q * A[ q , j ]
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
          q = head (queue ctd)
          r = estimate ctd

      visited : {t : Fin (suc n)} → ⌛ t → Subset (suc n)
      visited start        = ⁅ i ⁆
      visited (tick t ctd) = visited ctd ∪ ⁅ head (queue ctd) ⁆
        where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      visited-lemma : {t : Fin (suc n)} (ctd : ⌛ t) → Sub.size (visited ctd) ≡ suc n ∸ (toℕ t)
      visited-lemma start rewrite to-from n | sn∸n≡1 n = Sub.size⁅i⁆≡1 i
      visited-lemma (tick t ctd) =
        begin
          Sub.size (visited ctd ∪ ⁅ head (queue ctd) ⁆)
            ≡⟨ P.cong Sub.size (∪-comm (visited ctd) ⁅ head (queue ctd) ⁆) ⟩
          Sub.size (⁅ head (queue ctd) ⁆ ∪ visited ctd)
            ≡⟨ Sub.size-suc (head (queue ctd)) (visited ctd) (head∉visited ctd) ⟩
          suc (Sub.size (visited ctd))
            ≡⟨ P.cong suc (visited-lemma ctd) ⟩
          suc (suc n ∸ toℕ (suc t))
            ≡⟨ P.cong suc (lemma₀ n t) ⟩
          suc (n ∸ toℕ (inject₁ t))
            ≡⟨ P.sym (sm∸n n (toℕ (inject₁ t)) (lemma₁ n t)) ⟩
          suc n ∸ toℕ (inject₁ t)
        ∎
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)
          open P.≡-Reasoning
          open Sub.Properties (suc n)

          lemma₀ : ∀ n (t : Fin n) → suc n ∸ toℕ (suc t) ≡ n ∸ toℕ (inject₁ t)
          lemma₀ n t rewrite inject₁-lemma t = P.refl

          lemma₁ : ∀ n (t : Fin n) → toℕ (inject₁ t) N.≤ n
          lemma₁ n t rewrite inject₁-lemma t = suc-inj (≤-step (bounded t))

      size-lemma : ∀ {t} (ctd : ⌛ t) → Sub.size (∁ (visited ctd)) ≡ toℕ t
      size-lemma {t} ctd =
        begin
          Sub.size (∁ (visited ctd))      ≡⟨ Sub.∁-size (visited ctd) ⟩
          suc n ∸ Sub.size (visited ctd)  ≡⟨ P.cong₂ _∸_ P.refl (visited-lemma ctd) ⟩
          suc n ∸ (suc n ∸ toℕ t)         ≡⟨ ∸-assoc _ _ (toℕ t) ≤-refl (≤-step (suc-inj (bounded t))) ⟩
          (suc n ∸ suc n) N.+ toℕ t       ≡⟨ P.cong₂ N._+_ (n∸n≡0 (suc n)) P.refl ⟩
          toℕ t
        ∎
        where
          open P.≡-Reasoning

      queue′ : ∀ {t} (ctd : ⌛ t) →
               let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
               SortedVec (Sub.size $ ∁ $ visited ctd)
      queue′ ctd = fromVec $ Sub.toVec $ ∁ $ visited ctd
        where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      queue : ∀ {t} (ctd : ⌛ t) →
              let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
              SortedVec (toℕ t)
      queue {t} ctd = P.subst SortedVec (size-lemma ctd) (queue′ ctd)
        where open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      q′→q : ∀ {t} (ctd : ⌛ (suc t)) →
             let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
             ∀ {p} (P : ∀ {n} → SortedVec n → Set p) → P (queue′ ctd) → P (queue ctd)
      q′→q ctd P Pq′ = {!!}
        where
          open Sorted (estimateOrder $ V.tabulate $ estimate ctd)

      head∉visited : {t : Fin n} (ctd : ⌛ (suc t)) →
                     let open Sorted (estimateOrder $ V.tabulate $ estimate ctd) in
                     head (queue ctd) ∉ visited ctd
      head∉visited ctd q∈vs with queue ctd
      head∉visited ctd q∈vs | q Sorted.∷ qs ⟨ q≼qs ⟩ = q∉q∷qs (S.here qs q≼qs)
        where
          module S = Sorted (estimateOrder $ V.tabulate $ estimate ctd)

          q∉queue′ : ¬ q S.∈ (queue′ ctd)
          q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

          q∉queue : ¬ q S.∈ (queue ctd)
          q∉queue = q′→q ctd (λ qs → ¬ q S.∈ qs) q∉queue′

          q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
          q∉q∷qs = P.subst (λ qs → ¬ q S.∈ qs) {!P.refl!} q∉queue
      -- q ∈ visited ctd
      -- ⟶ q ∉ ∁ (visited ctd)   by Sub.∁-∈
      -- ⟶ q ∉ Sub.toVec (∁ (visited ctd))   by Sub.toVec-∉¹
      -- ⟶ q ∉ fromVec (Sub.toVec (∁ (visited ctd)))   by fromVec-∉¹
      -- ⟶ q ∉ P.subst SortedVec {! eq !} (fromVec (Sub.toVec (∁ (visited ctd))))

  RLS : {t : Fin (suc n)} → Pred (⌛ t) _
  RLS ctd = let r = estimate ctd in
    ∀ j → r j ≈ I[ i , j ] + (⨁[ q ← visited ctd ] (r j + r q * A[ q , j ]))

  init‿A≈I+A : (i j : Fin (suc n)) → A[ i , j ] ≈ I[ i , j ] + A[ i , j ]
  init‿A≈I+A i j with i ≟ j
  ... | yes i≡j rewrite i≡j = let open EqR setoid in
    begin
      A[ j , j ]               ≡⟨ Adj.diag adj j ⟩
      1#                       ≈⟨ sym (+-idempotent _) ⟩
      1#         + 1#          ≡⟨ P.sym (P.cong₂ _+_ (Adj.diag I j) (Adj.diag adj j)) ⟩
      I[ j , j ] + A[ j , j ]
    ∎
  ... | no ¬i≡j = let open EqR setoid in
    begin
      A[ i , j ]                       ≈⟨ sym (proj₁ +-identity _) ⟩
      0#                 + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl ⟩
      diagonal 0# 1# i j + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl ⟩
      I[ i , j ]         + A[ i , j ]
    ∎

  correct-init : RLS start
  correct-init j = trans (init‿A≈I+A i j) (+-cong refl lemma)
    where
      lemma =
        begin
          A[ i , j ]
            ≈⟨ sym (+-idempotent _) ⟩
          A[ i , j ] + A[ i , j ]
            ≈⟨ +-cong refl (sym (*-identityˡ _)) ⟩
          A[ i , j ] + 1# * A[ i , j ]
            ≈⟨ +-cong refl (*-cong (sym (reflexive (Adj.diag adj i))) refl) ⟩
          A[ i , j ] + A[ i , i ] * A[ i , j ]
            ≡⟨⟩
          r j + r i * A[ i , j ]
            ≈⟨ sym (fold-⁅i⁆ _ i) ⟩
          ⨁[ q ← ⁅ i ⁆ ] (r j + r q * A[ q , j ])
        ∎
        where
          open EqR setoid
          r = estimate start


{-

-}

{-
data State {n} (i : Fin (suc n)) (adj : Adj (suc n)) : ℕ → Set (ℓ ⊔ c) where
  init : State i adj n
  step : {m : ℕ} (prev : State i adj (suc m)) → State i adj m

estimate : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Fin (suc n) → Weight
visited : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} → State i adj m → Subset (suc n)
visited-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
                (Sub.size (visited state)) ≡ suc n ∸ m

state-lemma : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
              m N.≤ n
state-lemma init         = ≤-refl
state-lemma (step state) = suc-inj (≤-step (state-lemma state))

queue : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m) →
        let open Sorted (estimateOrder $ V.tabulate $ estimate state) in
        SortedVec m
queue {m} {n} state = P.subst SortedVec m-eq queue′
  where
    open P.≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
    open Sorted (estimateOrder $ V.tabulate $ estimate state)

    queue′ : SortedVec (Sub.size $ ∁ $ visited state)
    queue′ = fromVec $ Sub.toVec $ ∁ $ visited state

    m-eq : Sub.size (∁ (visited state)) ≡ m
    m-eq =
      start
        Sub.size (∁ (visited state))      ≣⟨ Sub.∁-size (visited state) ⟩
        suc n ∸ Sub.size (visited state)  ≣⟨ P.cong₂ _∸_ P.refl (visited-lemma state) ⟩
        suc n ∸ (suc n ∸ m)               ≣⟨ ∸-assoc _ _ m ≤-refl (≤-step (state-lemma state)) ⟩
        (suc n ∸ suc n) N.+ m             ≣⟨ P.cong₂ N._+_ (n∸n≡0 (suc n)) P.refl ⟩
        m
      □

visited {i = i} init         = ⁅ i ⁆
visited {i = i} (step state) = visited state ∪ ⁅ head (queue state) ⁆
  where open Sorted (estimateOrder $ V.tabulate $ estimate state)

module Abbreviations
    {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)} (state : State i adj m)
    where

  A[_,_] : Fin (suc n) → Fin (suc n) → Weight
  A[ i , j ] = Adj.matrix adj [ i , j ]

  r[_] : Fin (suc n) → Weight
  r[ j ] = estimate state j

estimate {i = i} {adj} init   j = A[ i , j ]
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
  ∀ j → r[ j ] ≈ I[ i , j ] + (⨁[ q ← visited state ] (r[ j ] + r[ q ] * A[ q , j ]))

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
    A[ i , j ]                       ≈⟨ sym (proj₁ +-identity _) ⟩
    0#                 + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl ⟩
    diagonal 0# 1# i j + A[ i , j ]  ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl ⟩
    I[ i , j ]         + A[ i , j ]
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
          ≡⟨⟩
        r[ j ] + r[ i ] * A[ i , j ]
          ≈⟨ sym (fold-⁅i⁆ _ i) ⟩
        ⨁[ q ← ⁅ i ⁆ ] (r[ j ] + r[ q ] * A[ q , j ])
      ∎

correct-step : {m n : ℕ} {i : Fin (suc n)} {adj : Adj (suc n)}
               (state : State i adj (suc m)) → RLS state → RLS (step state)
correct-step {i = i} state rls j = -- need to split on j ∈? visited state
  begin
    r[ j ] + r[ q ] * A[ q , j ]
      ≈⟨ +-cong (rls j) (*-cong eq refl) ⟩
    (I[ i , j ] + (⨁[ q ← qs ] (r[ j ] + r[ q ] * A[ q , j ]))) + r′[ q ] * A[ q , j ]
      ≈⟨ +-cong (+-cong refl (fold-cong _ _ qs (λ q q∈qs → +-cong (eq′ j {!!}) (*-cong (eq′ q q∈qs) refl)))) refl ⟩
    (I[ i , j ] + (⨁[ q ← qs ] (r′[ j ] + r′[ q ] * A[ q , j ]))) + r′[ q ] * A[ q , j ]
      ≈⟨ +-assoc _ _ _ ⟩
    I[ i , j ] + ((⨁[ q ← qs ] (r′[ j ] + r′[ q ] * A[ q , j ])) + r′[ q ] * A[ q , j ])
      ≈⟨ +-cong refl (+-cong (fold-distr′ +-idempotent _ r′[ j ] qs {!!}) refl) ⟩
    I[ i , j ] + ((r′[ j ] + ((⨁[ q ← qs ] (r′[ q ] * A[ q , j ]))) + r′[ q ] * A[ q , j ]))
      ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
    I[ i , j ] + (r′[ j ] + ((⨁[ q ← qs ] (r′[ q ] * A[ q , j ])) + r′[ q ] * A[ q , j ]))
      ≈⟨ +-cong refl (+-cong refl (+-cong refl (sym (fold-⁅i⁆ _ q)))) ⟩
    I[ i , j ] + (r′[ j ] + ((⨁[ q ← qs ] (r′[ q ] * A[ q , j ])) + (⨁[ q ← ⁅ q ⁆ ] (r′[ q ] * A[ q , j ]))))
      ≈⟨ +-cong refl (+-cong refl (sym (fold-∪ +-idempotent _ (visited state) ⁅ q ⁆))) ⟩
    I[ i , j ] + (r′[ j ] + (⨁[ q ← qs′ ] (r′[ q ] * A[ q , j ])))
      ≈⟨ +-cong refl (sym (fold-distr′ +-idempotent _ r′[ j ] qs′ {!!})) ⟩
    I[ i , j ] + (⨁[ q ← qs′ ] (r′[ j ] + r′[ q ] * A[ q , j ]))
  ∎
  where
    open Sorted (estimateOrder $ V.tabulate $ estimate state) hiding (_∈_)
    open Abbreviations state
    open Abbreviations (step state) using () renaming (r[_] to r′[_])
    q = head (queue state)
    qs = visited state
    qs′ = visited state ∪ ⁅ q ⁆

    eq : r[ q ] ≈ r′[ q ]
    eq = {!!}

    eq′ : ∀ j → j ∈ visited state → r[ j ] ≈ r′[ j ]
    eq′ j j∈queue = {!!}
-}
