open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Data.AVL.Properties
  {k v ℓ}
  {Key : Set k} (Value : Key → Set v)
  {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.AVL Value isStrictTotalOrder hiding (map)
import Data.DifferenceList as DiffList
open import Data.List.All hiding (map)
open import Data.List.Base
open import Data.Product hiding (map)
open import Level

open IsStrictTotalOrder isStrictTotalOrder
open Indexed hiding (map)
open Extended-key

data Ordered : List Key → Set (k ⊔ ℓ) where
  []  : Ordered []
  _∷_ : ∀ {x xs} (min : All (_<_ x) xs) (ord : Ordered xs) → Ordered (x ∷ xs)

toList-ordered : ∀ t → Ordered (map proj₁ (toList t))
toList-ordered (tree (leaf l<u)) = []
toList-ordered (tree (node (k , v) lk ku bal)) = {!!}
