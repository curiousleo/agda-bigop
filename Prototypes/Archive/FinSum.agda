module Prototypes.FinSum where

  open import Data.Fin hiding (compare)
  open import Data.Nat hiding (compare)
    renaming (_+_ to _N+_ ; _≤?_ to _N≤?_ ; _≤_ to _N≤_ ; _>_ to _N>_ ; _<_ to _N<_)
  open import Data.Nat.Properties
  open import Data.Sum
  open import Data.Product

  open import Function.Bijection hiding (_∘_)
  open import Function.Surjection hiding (_∘_)

  open import Relation.Binary
  open import Relation.Binary.Core
  open import Relation.Binary.PropositionalEquality
    using (refl ; cong ; sym ; trans ; setoid ; →-to-⟶)

  open import Relation.Nullary

  open import Prototypes.Injectivity

  m⊎n→m+n : ∀ {m n} → Fin m ⊎ Fin n → Fin (m N+ n)
  m⊎n→m+n {m} {n} = [ inject+ n , raise m ]′

  m+n→m⊎n : ∀ {m n} → Fin (m N+ n) → Fin m ⊎ Fin n
  m+n→m⊎n {m} {n} i with m N≤? toℕ i
  ... | yes m≤i = inj₂ (reduce≥ i m≤i)
  ... | no ¬m≤i = inj₁ (fromℕ≤ {toℕ i} (≰⇒> ¬m≤i))

  m⊎n↔m+n : ∀ {m n} →
            Bijection (setoid (Fin m ⊎ Fin n)) (setoid (Fin (m N+ n)))
  m⊎n↔m+n {m} {n} = record { to = to⟶ ; bijective = bijective }
    where
      open import Relation.Nullary
      open import Data.Fin.Properties hiding (strictTotalOrder)
      open import Function.LeftInverse using (_RightInverseOf_)
      open import Data.Empty

      open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder strictTotalOrder) using (compare)

      to⟶ = →-to-⟶ m⊎n→m+n

      theorem₀ : ∀ {n m} {j : Fin n} → ¬ m ≰ toℕ (raise m j)
      theorem₀ nleq = lemma₀ (lemma₁ nleq)
        where
          open import Data.Fin.Properties
          open import Data.Nat.Properties

          lemma₀ : ∀ {m n} → ¬ m N> m N+ n
          lemma₀ (s≤s gt) = lemma₀ gt

          lemma₁ : ∀ {n m} {j : Fin n} → m ≰ toℕ (raise m j) → m N> m N+ toℕ j
          lemma₁ {m = m} {j = j} leq rewrite toℕ-raise m j = ≰⇒> leq

      theorem₁ : ∀ {m n} {i⊎ : Fin m ⊎ Fin n} →
                 ∃ (λ i → inj₁ i ≡ i⊎) → m N> toℕ (m⊎n→m+n i⊎)
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

      injective : ∀ {i j : Fin m ⊎ Fin n} → m⊎n→m+n i ≡ m⊎n→m+n j → i ≡ j
      injective {i⊎} {j⊎} eq with m N≤? toℕ (m⊎n→m+n i⊎) | m N≤? toℕ (m⊎n→m+n j⊎)
      injective {inj₁ i} {inj₁ j} eq | _ | _ = cong inj₁ lemma
        where
          lemma : i ≡ j
          lemma = inject+k-injective i j eq
      injective {inj₂ i} {inj₂ j} eq | _ | _ = cong inj₂ lemma
        where
          lemma : i ≡ j
          lemma = raisek-injective m i j eq
      injective {inj₁ i} {inj₂ j} eq | yes m≤i | yes m≤j = ⊥-elim contradiction
        where
          contradiction = theorem₂ m≤i (theorem₁ {m} (i , refl))
      injective {inj₂ i} {inj₁ j} eq | yes m≤i | yes m≤j = ⊥-elim contradiction
        where
          contradiction = theorem₂ m≤j (theorem₁ {m} (j , refl))
      injective {inj₁ i} {inj₂ j} eq | no ¬m≤i | no ¬m≤j = ⊥-elim (theorem₀ ¬m≤j)
      injective {inj₂ i} {inj₁ j} eq | no ¬m≤i | no ¬m≤j = ⊥-elim (theorem₀ ¬m≤i)
      ... | yes m≤i | no ¬m≤j rewrite eq = ⊥-elim (¬m≤j m≤i)
      ... | no ¬m≤i | yes m≤j rewrite eq = ⊥-elim (¬m≤i m≤j)

      from⟶ = →-to-⟶ m+n→m⊎n

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
          right-inv : ∀ (k : Fin (m N+ n)) → m⊎n→m+n {m} {n} (m+n→m⊎n k) ≡ k
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

{-
  ⊎-bijection : ∀ {a b c d} →
                {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
                Bijection (setoid A) (setoid B) →
                Bijection (setoid C) (setoid D) →
                Bijection (setoid (A ⊎ C)) (setoid (B ⊎ D))
  ⊎-bijection {A = A} {B = B} {C = C} {D = D} A↔B C↔D = record {
    to = →-to-⟶ f ;
    bijective = record { injective = {!!} ; surjective = {!!} } }
    where
      open Bijection A↔B renaming (to to toAB ; bijective to bijAB)
      open Bijection C↔D renaming (to to toCD ; bijective to bijCD)

      open Surjective (Bijective.surjective bijAB) renaming (from to fromAB)
      open Surjective (Bijective.surjective bijCD) renaming (from to fromCD)

      open import Function using (_∘_)
      import Function.Equality hiding (cong)
      open Function.Equality.Π toAB renaming (_⟨$⟩_ to _⟨$⟩AB_ ; cong to congAB)
      open Function.Equality.Π toCD renaming (_⟨$⟩_ to _⟨$⟩CD_ ; cong to congCD)

      f : A ⊎ C → B ⊎ D
      f = [ inj₁ ∘ _⟨$⟩AB_ , inj₂ ∘ _⟨$⟩CD_ ]′

      inj : ∀ {x y : A ⊎ C} → f x ≡ f y → x ≡ y
      inj {inj₁ x} {inj₁ y} eq with A↔B ⟨$⟩AB x ≡ toAB ⟨$⟩AB y
      inj {inj₁ x} {inj₁ y} eq | eq′ = {!eq!}
      inj {inj₁ x} {inj₂ y} ()
      inj {inj₂ x} {inj₁ y} ()
      inj {inj₂ x} {inj₂ y} eq = cong inj₂ {!congCD!}
-}
