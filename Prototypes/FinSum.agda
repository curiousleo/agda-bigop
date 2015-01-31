module Prototypes.FinSum where

  open import Data.Fin hiding (compare)
  open import Data.Nat hiding (compare)
    renaming (_+_ to _N+_ ; _≤?_ to _N≤?_ ; _≤_ to _N≤_ ; _>_ to _N>_ ; _<_ to _N<_)
  open import Data.Sum
  open import Data.Product

  open import Function.Bijection
  open import Function.Surjection

  open import Relation.Binary.Core using (_≡_)
  open import Relation.Binary.PropositionalEquality
    using (refl ; cong ; sym ; trans ; setoid ; →-to-⟶)

  open import Relation.Nullary.Core using (¬_)

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

  theorem₀ : ∀ {n m} {j : Fin n} → ¬ m ≰ toℕ (raise m j)
  theorem₀ nleq = lemma₁ (lemma₀ nleq)
    where
      open import Data.Fin.Properties
      open import Data.Nat.Properties

      lemma₀ : ∀ {n m} {j : Fin n} → m ≰ toℕ (raise m j) → m N> m N+ toℕ j
      lemma₀ {m = m} {j = j} leq rewrite toℕ-raise m j = ≰⇒> leq

      lemma₁ : ∀ {m n} → ¬ m N> m N+ n
      lemma₁ (s≤s gt) = lemma₁ gt

  m⊎n↔m+n : ∀ {m n} →
            Bijection (setoid (Fin m ⊎ Fin n)) (setoid (Fin (m N+ n)))
  m⊎n↔m+n {m} {n} = record { to = to⟶ ; bijective = bijective }
    where
      open import Relation.Nullary
      open import Data.Fin.Properties hiding (strictTotalOrder)
      open import Data.Nat.Properties
      open import Function.LeftInverse using (_RightInverseOf_)
      open import Data.Empty

      open import Relation.Binary
      open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)
      
      from→ : ∀ {m n} → Fin (m N+ n) → Fin m ⊎ Fin n
      from→ {m} {n} i with m N≤? toℕ i
      ... | yes m≤i = inj₂ (reduce≥ i m≤i)
      ... | no ¬m≤i = inj₁ (fromℕ≤ {toℕ i} (≰⇒> ¬m≤i))

      to→ : ∀ {m n} → Fin m ⊎ Fin n → Fin (m N+ n)
      to→ {m} {n} = [ inject+ n , raise m ]′

      from⟶ = →-to-⟶ from→
      to⟶ = →-to-⟶ to→

      theorem₁ : ∀ {m n} {i⊎ : Fin m ⊎ Fin n} → ∃ (λ i → inj₁ i ≡ i⊎) → m N> toℕ (to→ i⊎)
      theorem₁ = {!!}

      theorem₂ : ∀ {m n} {j⊎ : Fin m ⊎ Fin n} → ∃ (λ j → inj₂ j ≡ j⊎) → m N≤ toℕ (to→ j⊎)
      theorem₂ = {!!}

      theorem₃ : ∀ {m n} → m N≤ n → n N< m → ⊥
      theorem₃ {m} {n} m≤n m>n with compare m n
      theorem₃ m≤n m>n | tri<  m<n ¬m≡n ¬n<m = ¬n<m m>n
      theorem₃ m≤n m>n | tri≈ ¬m<n  m≡n ¬n<m = ¬n<m m>n
      theorem₃ {m} {n} m≤n m>n | tri> ¬m<n ¬m≡n  n<m = {!!}
        where
          lemma₀ : m N≤ n → m ≡ n ⊎ m N< n
          lemma₀ m≤n with compare m n
          lemma₀ m≤n₁ | tri< a ¬b ¬c = inj₂ a
          lemma₀ m≤n₁ | tri≈ ¬a b ¬c = inj₁ b
          lemma₀ m≤n₁ | tri> ¬m<n ¬m≡n n<m = {!!}

      injective : ∀ {i j : Fin m ⊎ Fin n} → to→ i ≡ to→ j → i ≡ j
      injective {i⊎} {j⊎} eq with m N≤? toℕ (to→ i⊎) | m N≤? toℕ (to→ j⊎)
      injective {inj₁ i} {inj₁ j} eq | _ | _ = cong inj₁ (inject+k-injective i j eq)
      injective {inj₂ i} {inj₂ j} eq | _ | _ = cong inj₂ (raisek-injective m i j eq)
      injective {inj₁ i} {inj₂ j} eq | yes m≤i | yes m≤j = ⊥-elim (theorem₃ m≤i (theorem₁ {m} (i , refl)))
      injective {inj₂ i} {inj₁ j} eq | yes m≤i | yes m≤j = ⊥-elim (theorem₃ m≤j (theorem₁ {m} (j , refl)))
      injective {inj₁ i} {inj₂ j} eq | no ¬m≤i | no ¬m≤j = ⊥-elim (theorem₀ ¬m≤j)
      injective {inj₂ i} {inj₁ j} eq | no ¬m≤i | no ¬m≤j = ⊥-elim (theorem₀ ¬m≤i)
      ... | yes m≤i | no ¬m≤j rewrite eq = ⊥-elim (¬m≤j m≤i)
      ... | no ¬m≤i | yes m≤j rewrite eq = ⊥-elim (¬m≤i m≤j)

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ (k : Fin (m N+ n)) → to→ {m} {n} (from→ k) ≡ k -- from⟶ RightInverseOf to⟶
          right-inv k with m N≤? toℕ k | from→ {m} {n} k
          ... | m≤i | inj₁ k′  = toℕ-injective (sym {!!})
          ... | m≤i | inj₂ m-k = {!!}

      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }
