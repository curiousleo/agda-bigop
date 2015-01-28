module Prototypes.FinSum where

  open import Data.Fin hiding (compare)
  open import Data.Nat hiding (compare)
    renaming (_+_ to _N+_ ; _≤?_ to _N≤?_)
  open import Data.Sum

  open import Function.Bijection
  open import Function.Surjection

  open import Relation.Binary.Core using (_≡_)
  open import Relation.Binary.PropositionalEquality
    using (refl ; cong ; sym ; setoid ; →-to-⟶)

  suc-injective : ∀ {n} {p q : Fin n} → Fin.suc p ≡ suc q → p ≡ q
  suc-injective refl = refl

  inject+k-injective : ∀ {n k} → (i : Fin n) → (j : Fin n) →
                       inject+ k i ≡ inject+ k j → i ≡ j
  inject+k-injective zero zero inj≡ = refl
  inject+k-injective zero (suc j) ()
  inject+k-injective (suc i) zero ()
  inject+k-injective (suc i) (suc j) inj≡ = cong suc (inject+k-injective i j (suc-injective inj≡))

  raisek-injective : ∀ {n} → (k : ℕ) → (i : Fin n) → (j : Fin n) →
                     raise k i ≡ raise k j → i ≡ j
  raisek-injective zero i .i refl = refl
  raisek-injective (suc k) i j r≡r = raisek-injective k i j (suc-injective r≡r)

  m+n↔n+m : ∀ {m n} →
            Bijection (setoid (Fin (m N+ n))) (setoid (Fin (n N+ m)))
  m+n↔n+m {m} {n} = {!!}

  inject+-raise-injective : (m n : ℕ) → (i : Fin n) → (j : Fin m) →
                            inject+ m i ≡ raise n j → toℕ i ≡ n N+ toℕ j
  inject+-raise-injective m n i j inj≡ =
    begin
      toℕ i
        ≡⟨ inject+-lemma m i ⟩
      toℕ (inject+ m i)
        ≡⟨ cong toℕ inj≡ ⟩
      toℕ (raise n j)
        ≡⟨ toℕ-raise n j ⟩
      n N+ toℕ j
    ∎
    where
      open Relation.Binary.PropositionalEquality.≡-Reasoning
      open import Data.Fin.Properties

  m⊎n↔m+n : ∀ {m n} →
            Bijection (setoid (Fin (suc m) ⊎ Fin n))
                      (setoid (Fin (suc m N+ n)))
  m⊎n↔m+n {m} {n} = record { to = to⟶ ; bijective = bijective }
    where
      open import Data.Fin.Properties hiding (strictTotalOrder)
      open import Data.Nat.Properties
      open import Function.LeftInverse using (_RightInverseOf_)
      open import Relation.Nullary

      open import Relation.Binary
      open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder
                               strictTotalOrder)
      
      from→ : ∀ {m n} → Fin (suc m N+ n) → Fin (suc m) ⊎ Fin n
      from→ {m} i with suc m N≤? toℕ i
      ... | yes m≤i = inj₂ (reduce≥ i m≤i)
      ... | no ¬m≤i = inj₁ (fromℕ≤ {toℕ i} (≰⇒> ¬m≤i))

      to→ : ∀ {m n} → Fin (suc m) ⊎ Fin n → Fin (suc m N+ n)
      to→ {m} {n} = [ inject+ n , raise (suc m) ]′

      from⟶ = →-to-⟶ from→
      to⟶ = →-to-⟶ to→

      injective : ∀ {i j : Fin (suc m) ⊎ Fin n} → to→ i ≡ to→ j → i ≡ j
--    injective {i⊎} {j⊎} eq with i⊎ | j⊎
--    ... | inj₁ i′ | inj₁ j′ = cong inj₁ (inject+k-injective {m} i′ j′ eq)
--    ... | inj₁ i′ | inj₂ j′ = {!inject+-raise-injective!}
--    ... | inj₂ i′ | inj₁ j′ = {!!}
--    ... | inj₂ i′ | inj₂ j′ = cong inj₂ (raisek-injective m i′ j′ eq)
      injective {i⊎} {j⊎} eq with i⊎ | j⊎
      injective eq | inj₁ i′ | inj₁ j′ = cong inj₁ (inject+k-injective i′ j′ eq)
      injective eq | inj₁ i′ | inj₂ j′ with (toℕ i′) N≤? (toℕ j′)
      injective eq | inj₁ i′ | inj₂ j′ | yes p = {!!}
      injective eq | inj₁ i′ | inj₂ j′ | no ¬p = {!!}
      injective eq | inj₂ y | inj₁ x = {!!}
      injective eq | inj₂ y | inj₂ y₁ = cong inj₂ (raisek-injective m y y₁ (suc-injective eq))

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ (k : Fin (suc m N+ n)) → to→ {m} {n} (from→ k) ≡ k -- from⟶ RightInverseOf to⟶
          right-inv k with m N≤? toℕ k | from→ {m} {n} k
          ... | m≤i | inj₁ k′  = toℕ-injective (sym {!!})
          ... | m≤i | inj₂ m-k = {!!}

      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }
