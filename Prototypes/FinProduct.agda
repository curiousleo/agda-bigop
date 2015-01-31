module Prototypes.FinProduct where

  open import Data.Fin hiding (compare)
  open import Data.Nat hiding (compare)
    renaming (_+_ to _N+_ ; _≤?_ to _N≤?_ ; _≤_ to _N≤_ ; _>_ to _N>_ ; _<_ to _N<_)
  open import Data.Sum
  open import Data.Product

  open import Function.Bijection hiding (_∘_)
  open import Function.Surjection hiding (_∘_)

  open import Relation.Binary.Core using (_≡_)
  open import Relation.Binary.PropositionalEquality
    using (refl ; cong ; sym ; trans ; setoid ; →-to-⟶)

  open import Relation.Nullary.Core using (¬_)

  open import Prototypes.Injectivity

  m×n↔m+n : ∀ {m n} →
            Bijection (setoid (Fin m × Fin n)) (setoid (Fin (m * n)))
  m×n↔m+n {m} {n} = record { to = to⟶ ; bijective = bijective }
    where
      open import Relation.Nullary
      open import Data.Fin.Properties hiding (strictTotalOrder)
      open import Data.Nat.Properties
      open import Function.LeftInverse using (_RightInverseOf_)
      open import Data.Empty

      open import Relation.Binary
      open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)
      
      from→ : ∀ {m n} → Fin (m * n) → Fin m × Fin n
      from→ {m} {n} i = ?

      to→ : ∀ {m n} → Fin m × Fin n → Fin (m * n)
      to→ {m} {n} (i , j) = ?

      from⟶ = →-to-⟶ from→
      to⟶ = →-to-⟶ to→

      injective : ∀ {i j : Fin m × Fin n} → to→ i ≡ to→ j → i ≡ j
      injective {i⊎} {j⊎} eq = ?

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ (k : Fin (m * n)) → to→ {m} {n} (from→ k) ≡ k -- from⟶ RightInverseOf to⟶
          right-inv k = ?

      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }
