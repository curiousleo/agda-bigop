open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Dijkstra.PriorityQueue
  {k ℓ}
  {Key : Set k}
  {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.List.All hiding (map)
open import Data.List.Base
open import Data.Maybe hiding (All; map)
open import Data.Product hiding (map)
open import Level
open import Relation.Unary

open IsStrictTotalOrder isStrictTotalOrder

data Ordered : List Key → Set (k ⊔ ℓ) where
  []  : Ordered []
  _∷_ : ∀ {k pq} (min : All (_<_ k) pq) (ord : Ordered pq) → Ordered (k ∷ pq)

PQ = Σ (List Key) Ordered

All-→ : ∀ {a p q} {A : Set a} (xs : List A) {P : Pred A p} {Q : Pred A q} →
        P ⊆ Q → All P xs → All Q xs
All-→ []       P⊆Q all-p = []
All-→ (x ∷ xs) P⊆Q (px ∷ all-p) = (P⊆Q px) ∷ (All-→ xs P⊆Q all-p)

sort : List Key → PQ
sort [] = [] , []
sort (x ∷ xs) with sort xs
... | [] , [] = [] , []
... | y ∷ ys , min ∷ ord with compare x y
... | tri< a ¬b ¬c = (x ∷ (y ∷ ys)) , ((a ∷ (All-→ ys (trans a) min)) ∷ (min ∷ ord))
... | tri≈ ¬a b ¬c = (y ∷ ys) , (min ∷ ord)
... | tri> ¬a ¬b c = (y ∷ proj₁ (sort (x ∷ ys))) , ({!!} ∷ {!!})

insert : Key → PQ → PQ
insert k ([] , ord) = [ k ] , ([] ∷ ord)
insert k ((k′ ∷ pq) , min ∷ ord) with compare k k′
... | tri< k<k′ _ _ = (k ∷ (k′ ∷ pq) , ((k<k′ ∷ All-→ pq (trans k<k′) min) ∷ (min ∷ ord)))
... | tri≈ _ k≡k′ _ = k′ ∷ pq , min ∷ ord
... | tri> _ _ k′<k with insert k (pq , ord)
... | ([]  , [])   = {!!}
... | k″ ∷ pq″ , min′ ∷ ord′ = k′ ∷ (k″ ∷ pq″) , ({!!} ∷ {!!}) ∷ {!!} -- (k′ ∷ pq′) , {!!} ∷ ord′ -- (k′ , v′) ∷ (insert k v pq)

peek : PQ → Maybe Key
peek ([] , _)        = nothing
peek ((k ∷ pq) , _) = just k

pop : PQ → Maybe (Key × PQ)
pop ([] , _)        = nothing
pop ((k ∷ pq) , _) = just (k , {!!})

-- postulate
--   insert-ordered : ∀ k v pq → Ordered pq → Ordered (insert k v pq)

{-
insert-ordered : ∀ k v pq → Ordered pq → Ordered (insert k v pq)
insert-ordered k v [] pq-ord = [] ∷ pq-ord
insert-ordered k v ((k′ , v′) ∷ pq) (min ∷ pq-ord) with compare k k′
... | tri< k<k′ _ _ = (k<k′ ∷ {!min!}) ∷ (min ∷ pq-ord)
... | tri≈ _ k≡k′ _ = min ∷ pq-ord
... | tri> _ _ k′<k = {!!} ∷ (insert-ordered k v pq pq-ord)
-}
