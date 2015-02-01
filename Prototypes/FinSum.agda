module Prototypes.FinSum where

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
      open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder) using (compare)

      to→ : ∀ {m n} → Fin m ⊎ Fin n → Fin (m N+ n)
      to→ {m} {n} = [ inject+ n , raise m ]′

      to⟶ = →-to-⟶ to→

      theorem₀ : ∀ {n m} {j : Fin n} → ¬ m ≰ toℕ (raise m j)
      theorem₀ nleq = lemma₀ (lemma₁ nleq)
        where
          open import Data.Fin.Properties
          open import Data.Nat.Properties

          lemma₁ : ∀ {n m} {j : Fin n} → m ≰ toℕ (raise m j) → m N> m N+ toℕ j
          lemma₁ {m = m} {j = j} leq rewrite toℕ-raise m j = ≰⇒> leq

          lemma₀ : ∀ {m n} → ¬ m N> m N+ n
          lemma₀ (s≤s gt) = lemma₀ gt

      theorem₁ : ∀ {m n} {i⊎ : Fin m ⊎ Fin n} →
                 ∃ (λ i → inj₁ i ≡ i⊎) → m N> toℕ (to→ i⊎)
      theorem₁ {n = n} {i⊎ = inj₁ i} (_ , eq)
        rewrite eq | sym (inject+-lemma n i) = bounded i
      theorem₁ {i⊎ = inj₂ j} (i , ())

      theorem₂ : ∀ {m n} → m N≤ n → n N< m → ⊥
      theorem₂ {m} {n} m≤n m>n with compare m n
      theorem₂ m≤n m>n | tri<  m<n ¬m≡n ¬n<m = ¬n<m m>n
      theorem₂ m≤n m>n | tri≈ ¬m<n  m≡n ¬n<m = ¬n<m m>n
      theorem₂ {m} {n} m≤n m>n | tri> ¬m<n ¬m≡n  n<m = ⊥-elim contradiction
        where
          open import Function using (_∘_)

          lemma : ∀ {m n} → m N≤ n → m ≡ n ⊎ m N< n
          lemma {zero}  {zero}  z≤n = inj₁ refl
          lemma {zero}  {suc _} z≤n = inj₂ (s≤s z≤n)
          lemma {suc _} {zero}  ()
          lemma {suc m} {suc n} (s≤s m≤n) = [ inj₁ ∘ suc-surjective , inj₂ ∘ s≤s ]′ (lemma m≤n)
            where
              suc-surjective : ∀ {m n} → m ≡ n → Data.Nat.suc m ≡ suc n
              suc-surjective {zero} {zero} refl = refl
              suc-surjective {zero} {suc _} ()
              suc-surjective {suc _} {zero} ()
              suc-surjective {suc _} {suc _} eq = cong suc eq

          contradiction = ([ ¬m≡n , ¬m<n ]′ (lemma m≤n))

      injective : ∀ {i j : Fin m ⊎ Fin n} → to→ i ≡ to→ j → i ≡ j
      injective {i⊎} {j⊎} eq with m N≤? toℕ (to→ i⊎) | m N≤? toℕ (to→ j⊎)
      injective {inj₁ i} {inj₁ j} eq | _ | _ = cong inj₁ (inject+k-injective i j eq)
      injective {inj₂ i} {inj₂ j} eq | _ | _ = cong inj₂ (raisek-injective m i j eq)
      injective {inj₁ i} {inj₂ j} eq | yes m≤i | yes m≤j = ⊥-elim (theorem₂ m≤i (theorem₁ {m} (i , refl)))
      injective {inj₂ i} {inj₁ j} eq | yes m≤i | yes m≤j = ⊥-elim (theorem₂ m≤j (theorem₁ {m} (j , refl)))
      injective {inj₁ i} {inj₂ j} eq | no ¬m≤i | no ¬m≤j = ⊥-elim (theorem₀ ¬m≤j)
      injective {inj₂ i} {inj₁ j} eq | no ¬m≤i | no ¬m≤j = ⊥-elim (theorem₀ ¬m≤i)
      ... | yes m≤i | no ¬m≤j rewrite eq = ⊥-elim (¬m≤j m≤i)
      ... | no ¬m≤i | yes m≤j rewrite eq = ⊥-elim (¬m≤i m≤j)

      from→ : ∀ {m n} → Fin (m N+ n) → Fin m ⊎ Fin n
      from→ {m} {n} i with m N≤? toℕ i
      ... | yes m≤i = inj₂ (reduce≥ i m≤i)
      ... | no ¬m≤i = inj₁ (fromℕ≤ {toℕ i} (≰⇒> ¬m≤i))

      from⟶ = →-to-⟶ from→

      >⇒≰ : _N>_ ⇒ _≰_
      >⇒≰ (s≤s x) (s≤s y) = >⇒≰ x y

      reduce≥-lemma : ∀ {m n} → (i : Fin (m N+ n)) (m≤i : m N≤ toℕ i) →
                      m N+ toℕ (reduce≥ i m≤i) ≡ toℕ i
      reduce≥-lemma {zero} i m≤i = refl
      reduce≥-lemma {suc m} zero ()
      reduce≥-lemma {suc m} (suc i) (s≤s m≤i) = cong suc (reduce≥-lemma i m≤i)

      to-from≤ : ∀ {m k} → (m>k : m N> k) → toℕ (fromℕ≤ {k} {m} m>k) ≡ k
      to-from≤ (s≤s z≤n) = refl
      to-from≤ (s≤s (s≤s m>k)) = cong suc (to-from≤ (s≤s m>k))

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ (k : Fin (m N+ n)) → to→ {m} {n} (from→ k) ≡ k
          right-inv k with m N≤? toℕ k
          right-inv k | yes m≤k = toℕ-injective (trans lemma₀ lemma₁)
            where
              lemma₀ : toℕ (raise m (reduce≥ k m≤k)) ≡ m N+ toℕ (reduce≥ k m≤k)
              lemma₀ = toℕ-raise m (reduce≥ k m≤k)

              lemma₁ : m N+ toℕ (reduce≥ k m≤k) ≡ toℕ k
              lemma₁ = reduce≥-lemma k m≤k
          right-inv k | no ¬m≤k = toℕ-injective (trans lemma₀ lemma₁)
            where
              m>k : m N> toℕ k
              m>k = ≰⇒> ¬m≤k

              lemma₀ : toℕ (inject+ n (fromℕ≤ m>k)) ≡ toℕ (fromℕ≤ m>k)
              lemma₀ = sym (inject+-lemma n (fromℕ≤ m>k))

              lemma₁ : toℕ (fromℕ≤ m>k) ≡ toℕ k
              lemma₁ = to-from≤ m>k


      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }
