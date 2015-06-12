open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

module Dijkstra.State
  {a ℓ₁ ℓ₂}
  {A : Set a}
  {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂}
  (sto : IsStrictTotalOrder _≈_ _<_)
  where

import Data.AVL.Sets as Sets
open import Data.Fin using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base
import Data.Vec.Sorted as Sorted
open import Data.Product
open import Data.Vec
open import Level

open IsStrictTotalOrder sto
  renaming ( trans to sto-trans
           ; compare to sto-compare
           ; <-resp-≈ to sto-resp)
open IsEquivalence isEquivalence

module EstimateOrder {n} (est : Vec A n) where

  _<ᵉ_ : Fin n → Fin n → Set _
  a <ᵉ b = lookup a est < lookup b est

  _≈ᵉ_ : Rel (Fin n) _
  a ≈ᵉ b = lookup a est ≈ lookup b est

  isStrictTotalOrder : IsStrictTotalOrder _≈ᵉ_ _<ᵉ_
  isStrictTotalOrder =
    record
      { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
      ; trans         = sto-trans
      ; compare       = compare
      ; <-resp-≈      = <ᵉ-resp-≈ᵉ
      }
    where
      compare : Trichotomous _≈ᵉ_ _<ᵉ_
      compare m n with sto-compare (lookup m est) (lookup n est)
      ... | tri< a ¬b ¬c = tri< a ¬b ¬c
      ... | tri≈ ¬a b ¬c = tri≈ ¬a b ¬c
      ... | tri> ¬a ¬b c = tri> ¬a ¬b c

      <ᵉ-resp-≈ᵉ : _<ᵉ_ Respects₂ _≈ᵉ_
      <ᵉ-resp-≈ᵉ =
        (λ y≈ᵉy′ x<ᵉy → proj₁ sto-resp y≈ᵉy′ x<ᵉy) ,
        (λ y≈ᵉy′ y<ᵉx → proj₂ sto-resp y≈ᵉy′ y<ᵉx)

record DijkstraState (n : ℕ) : Set (a ⊔ ℓ₂) where
  field
    estimate : Vec A n
    unseen   : Fin n

  open EstimateOrder estimate
  open Sorted isStrictTotalOrder

  field
    queue    : SortedVec n
--  paths : {!!}
