open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

module Dijkstra.State
       {a ℓ} {A : Set a}
       (_<_ : Rel A ℓ)
       (sto : IsStrictTotalOrder _≡_ _<_)
       where

import Data.AVL.Sets as Sets
open import Data.Fin using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base
open import Data.Product
open import Data.Vec
open import Level

open IsStrictTotalOrder sto
  renaming ( trans to sto-trans
           ; compare to sto-compare
           ; <-resp-≈ to sto-resp)
open IsEquivalence isEquivalence

Fin-isStrictTotalOrder : (n : ℕ) → IsStrictTotalOrder _ _
Fin-isStrictTotalOrder n = StrictTotalOrder.isStrictTotalOrder (strictTotalOrder n)
  where
    open import Data.Fin.Properties

module Estimate {n} (est : Vec A n) where

  _<ᵉ_ : Fin n → Fin n → Set _
  a <ᵉ b = lookup a est < lookup b est

  _≈_ : Rel (Fin n) _
  a ≈ b = lookup a est ≡ lookup b est

  estimate-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<ᵉ_
  estimate-isStrictTotalOrder =
    record
      { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
      ; trans         = sto-trans
      ; compare       = compare
      ; <-resp-≈      = <ᵉ-resp-≈
      }
    where
      compare : Trichotomous _≈_ _<ᵉ_
      compare m n with sto-compare (lookup m est) (lookup n est)
      ... | tri< a ¬b ¬c = tri< a ¬b ¬c
      ... | tri≈ ¬a b ¬c = tri≈ ¬a b ¬c
      ... | tri> ¬a ¬b c = tri> ¬a ¬b c

      <ᵉ-resp-≈ : _<ᵉ_ Respects₂ _≈_
      <ᵉ-resp-≈ =
        (λ y≈y′ x<ᵉy → proj₁ sto-resp y≈y′ x<ᵉy) ,
        (λ y≈y′ y<ᵉx → proj₂ sto-resp y≈y′ y<ᵉx)

record DijkstraState (n : ℕ) : Set (a ⊔ ℓ) where
  field
    estimate : Vec A n

--  open Estimate estimate
--  open Sets estimate-isStrictTotalOrder
  open Sets (Fin-isStrictTotalOrder n)
  field
    visited  : ⟨Set⟩
    queue    : ⟨Set⟩
--  paths : {!!}
