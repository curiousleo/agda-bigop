open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

module Dijkstra.EstimateOrder
  {c ℓ₁ ℓ₂}
  (ord : TotalOrder c ℓ₁ ℓ₂)
  where

open import Data.Fin using (Fin)
open import Data.Sum
open import Data.Vec

open import Function

open TotalOrder ord renaming (Carrier to Weight)

estimateOrder : ∀ {n} (est : Vec Weight n) → TotalOrder _ _ _
estimateOrder {n} est =
  record
    { Carrier      = Fin n
    ; _≈_          = _≈ᵉ_
    ; _≤_          = _≤ᵉ_
    ; isTotalOrder =
      record
        { isPartialOrder =
            record
              { isPreorder =
                  record
                    { isEquivalence =
                        record
                          { refl  = ≈-refl
                          ; sym   = ≈-sym
                          ; trans = ≈-trans
                          }
                    ; reflexive = reflexive
                    ; trans     = trans
                    }
              ; antisym = antisym
              }
        ; total = totalᵉ
        }
    }
  where
    open IsEquivalence isEquivalence
      using ()
      renaming ( refl to ≈-refl
               ; sym to ≈-sym
               ; trans to ≈-trans
               )

    infix 4 _≈ᵉ_ _≤ᵉ_
    _≈ᵉ_ _≤ᵉ_ : Rel (Fin n) _
    _≈ᵉ_ = _≈_ on flip lookup est
    _≤ᵉ_ = _≤_ on flip lookup est

    totalᵉ : Total _≤ᵉ_
    totalᵉ a b with total (lookup a est) (lookup b est)
    ... | inj₁ estᵃ≤estᵇ = inj₁ estᵃ≤estᵇ
    ... | inj₂ estᵇ≤estᵃ = inj₂ estᵇ≤estᵃ
