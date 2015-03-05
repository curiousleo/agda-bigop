{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Prototypes.BigopFold where

  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary hiding (Decidable)
  open import Relation.Binary.PropositionalEquality

  open import Data.Empty
  open import Data.Product
  open import Data.Nat hiding (fold)
  open import Data.Vec hiding (_∈_; sum)

  open import Function

  open import Level renaming (zero to zeroL)

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core using (Op₂)

  fold : ∀ {i r ℓ} {I : Set i} {R : Set r} {n} →
         (I → R) → Op₂ R → {P′ : Pred I ℓ} → Decidable P′ → R → Vec I n → R
  fold {I = I} {R} f _∙_ p = foldr (λ _ → R) g
    where
      g : I → R → R
      g i acc with p i
      ... | yes _ = f i ∙ acc
      ... | no  _ = acc

  sum : ∀ {i ℓ} {I : Set i} {n} →
        (I → ℕ) → {P′ : Pred I ℓ} → Decidable P′ → Vec I n → ℕ
  sum f p = fold f _+_ p 0

  prod : ∀ {i ℓ} {I : Set i} {n} →
         (I → ℕ) → {P′ : Pred I ℓ} → Decidable P′ → Vec I n → ℕ
  prod f p = fold f _*_ p 1

  syntax sum (λ x → e) p = ∑ x ∈ p [ e ]

  module FoldLemmas
         {i r ℓ} {I : Set i} {R : Set r}
         (f : I → R) (_∙_ : Op₂ R) {P′ : Pred I ℓ}
         (P : Decidable P′) (ε : R) where

    empty-lemma : ∀ {n} (is : Vec I n) → Empty P′ → fold f _∙_ P ε is ≡ ε
    empty-lemma []       e = refl
    empty-lemma (i ∷ is) e with P i
    ... | yes p = ⊥-elim (e i p)
    ... | no ¬p = empty-lemma is e

    ∈-lemma : ∀ {n} (i : I) (is : Vec I n) →
              i ∈ P′ → fold f _∙_ P ε (i ∷ is) ≡ f i ∙ fold f _∙_ P ε is
    ∈-lemma i is i∈P′ with P i
    ... | yes p = refl
    ... | no ¬p = ⊥-elim (¬p i∈P′)

    ∉-lemma : ∀ {n} (i : I) (is : Vec I n) →
              i ∉ P′ → fold f _∙_ P ε (i ∷ is) ≡ fold f _∙_ P ε is
    ∉-lemma i is i∉P′ with P i
    ... | yes p = ⊥-elim (i∉P′ p)
    ... | no ¬p = refl

  module PQFoldLemmas
         {i r ℓ} {I : Set i} {R : Set r} (f : I → R) (_∙_ : Op₂ R)
         {P′ : Pred I ℓ} (P : Decidable P′)
         {Q′ : Pred I ℓ} (Q : Decidable Q′) (ε : R) where

    pred-lemma : ∀ {n} (is : Vec I n) →
                 P′ ⊆ Q′ → P′ ⊇ Q′ → fold f _∙_ P ε is ≡ fold f _∙_ Q ε is
    pred-lemma []       _   _   = refl
    pred-lemma (i ∷ is) P⊆Q P⊇Q with P i | Q i
    ... | yes p | yes q = cong (_∙_ (f i)) (pred-lemma is P⊆Q P⊇Q)
    ... | no ¬p | no ¬q = pred-lemma is P⊆Q P⊇Q
    ... | yes p | no ¬q = ⊥-elim (¬q (P⊆Q p))
    ... | no ¬p | yes q = ⊥-elim (¬p (P⊇Q q))


  module SemigroupFoldLemmas
         {i r ℓ₁ ℓ₂} {I : Set i} (S : Semigroup r ℓ₁)
         (f : I → Semigroup.Carrier S)
         {P′ : Pred I ℓ₂} (P : Decidable P′)
         (ε : Semigroup.Carrier S) where

    open Semigroup S hiding (refl)

    open FoldLemmas f _∙_ P ε


  module MonoidFoldLemmas
         {i r ℓ₁ ℓ₂} {I : Set i} (M : Monoid r ℓ₁)
         (f : I → Monoid.Carrier M)
         {P′ : Pred I ℓ₂} (P : Decidable P′) where

    open Monoid M

    open SemigroupFoldLemmas semigroup f P ε


  module CommutativeMonoidFoldLemmas
         {i r ℓ₁ ℓ₂} {I : Set i} (M : CommutativeMonoid r ℓ₁)
         (f : I → CommutativeMonoid.Carrier M)
         {P′ : Pred I ℓ₂} (P : Decidable P′) where

    open CommutativeMonoid M

    open MonoidFoldLemmas monoid f P


  module NearSemiringFoldLemmas
         {i r ℓ₁ ℓ₂} {I : Set i} (S : NearSemiring r ℓ₁)
         (f : I → NearSemiring.Carrier S)
         {P′ : Pred I ℓ₂} (P : Decidable P′) where

    open NearSemiring S

    open MonoidFoldLemmas +-monoid f P
    open SemigroupFoldLemmas *-semigroup f P 0#
