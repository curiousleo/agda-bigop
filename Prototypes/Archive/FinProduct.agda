module Prototypes.FinProduct where

  open import Data.Fin hiding (compare)
  open import Data.Nat hiding (compare ; fold)
    renaming (_+_ to _N+_ ; _*_ to _N*_ ; _≤?_ to _N≤?_ ; _≤_ to _N≤_ ; _>_ to _N>_ ; _<_ to _N<_)
  open import Data.Sum
  open import Data.Product

  open import Function.Bijection hiding (_∘_)
  open import Function.Surjection hiding (_∘_)

  open import Relation.Binary.Core using (_≡_)
  open import Relation.Binary.PropositionalEquality
    using (refl ; cong ; sym ; trans ; setoid ; →-to-⟶)

  open import Relation.Nullary.Core using (¬_)

  open import Prototypes.Injectivity

  m×n↔m*n : ∀ {m n} →
            Bijection (setoid (Fin m × Fin n)) (setoid (Fin (m N* n)))
  m×n↔m*n {m} {n} = record { to = to⟶ ; bijective = bijective }
    where
      open import Relation.Nullary
      open import Data.Fin.Properties hiding (_≟_ ; strictTotalOrder)
      open import Data.Nat.Properties
      open import Data.Nat.Properties.Simple
      open import Function.LeftInverse using (_RightInverseOf_)
      open import Data.Empty

      open import Relation.Binary
--    open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)

      _*_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (m N* n)
      _*_ {m} {n} i j = fromℕ≤ {toℕ i N* toℕ j} {m N* n} i*j<m*n
        where
          i<m : suc (toℕ i) N≤ m
          i<m = {!!}

          j<n : suc (toℕ j) N≤ n
          j<n = {!!}
          
          i*j<m*n : suc (toℕ i N* toℕ j) N≤ m N* n
          i*j<m*n = {!!}
            where
              open DecTotalOrder decTotalOrder
                renaming (trans to trans′) hiding (refl)

              lemma₀ : suc (toℕ i) N* suc (toℕ j) N≤ m N* n
              lemma₀ = i<m *-mono j<n

              lemma₁ : ∀ {i j} → i N* j N≤ i N* suc j
              lemma₁ {zero}  {j}     = z≤n
              lemma₁ {suc i} {zero} rewrite *-right-zero i = z≤n
              lemma₁ {suc i} {suc j} = {!!}

              lemma₂ : ∀ {i j k} → i N* suc j N≤ k N+ i N* suc j
              lemma₂ = {!!}

              lemma₃ : suc (toℕ i N* toℕ j) N≤ suc (toℕ i) N* suc (toℕ j)
              lemma₃ = s≤s (trans′ lemma₁ lemma₂) -- ({!!} *-mono {!!})

      to→ : ∀ {m n} → Fin m × Fin n → Fin (m N* n)
      to→ {m} {n} (i , j) = i * j

      to⟶ = →-to-⟶ to→

      from→ : ∀ {m n} → Fin (m N* n) → Fin m × Fin n
      from→ {m} {n} k with m N* n ≟ zero
      from→ {m} {n} k | yes p = {!!}
      from→ {m} {n} k | no ¬p = {!!}
{-
      from→ {suc m} {suc n} (suc k) = fromℕ≤ {quotient} {!!} , remainder
        where
          open import Data.Nat.DivMod
          open DivMod (suc (toℕ k) divMod (suc n))
-}
      from⟶ = →-to-⟶ from→


      injective : ∀ {i j : Fin m × Fin n} → to→ i ≡ to→ j → i ≡ j
      injective {i⊎} {j⊎} eq = {!!}

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ (k : Fin (m N* n)) → to→ {m} {n} (from→ k) ≡ k -- from⟶ RightInverseOf to⟶
          right-inv k = {!!}

      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }
