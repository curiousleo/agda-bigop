open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Dijkstra.PriorityQueue
  {k v ℓ}
  {Key : Set k} (Value : Key → Set v)
  {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.List.All hiding (map)
open import Data.List.Base
open import Data.Maybe hiding (All; map)
open import Data.Product hiding (map)
open import Level

open IsStrictTotalOrder isStrictTotalOrder

KV = Σ Key Value
PQ = List KV

insert : (k : Key) → Value k → PQ → PQ
insert k v [] = [ k , v ]
insert k v ((k′ , v′) ∷ pq) with compare k k′
... | tri< k<k′ _ _ = (k , v) ∷ (k′ , v′) ∷ pq
... | tri≈ _ k≡k′ _ = (k′ , v′) ∷ pq
... | tri> _ _ k′<k = (k′ , v′) ∷ (insert k v pq)

peek : PQ → Maybe KV
peek []        = nothing
peek (kv ∷ pq) = just kv

pop : PQ → Maybe (KV × PQ)
pop []        = nothing
pop (kv ∷ pq) = just (kv , pq)

data Ordered : PQ → Set (k ⊔ v ⊔ ℓ) where
  []  : Ordered []
  _∷_ : ∀ {kv pq} (min : All (_<_ (proj₁ kv)) (map proj₁ pq))
                  (ord : Ordered pq) →
                  Ordered (kv ∷ pq)

postulate
  insert-ordered : ∀ k v pq → Ordered pq → Ordered (insert k v pq)

{-
insert-ordered : ∀ k v pq → Ordered pq → Ordered (insert k v pq)
insert-ordered k v [] pq-ord = [] ∷ pq-ord
insert-ordered k v ((k′ , v′) ∷ pq) (min ∷ pq-ord) with compare k k′
... | tri< k<k′ _ _ = (k<k′ ∷ {!min!}) ∷ (min ∷ pq-ord)
... | tri≈ _ k≡k′ _ = min ∷ pq-ord
... | tri> _ _ k′<k = {!!} ∷ (insert-ordered k v pq pq-ord)
-}
