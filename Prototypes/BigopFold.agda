{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Prototypes.BigopFold where

  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary hiding (Decidable)
  import Relation.Binary.EqReasoning as EqR

  open import Data.Empty
  open import Data.Unit.Base
  open import Data.Product hiding (map)
  open import Data.Fin hiding (_+_; fold)
  open import Data.Nat hiding (fold)
  open import Data.Vec hiding (_∈_; sum)

  open import Function
  import Function.Equality as FEq

  open import Level renaming (zero to zeroL; suc to sucL)

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties

  fold : ∀ {i r ℓ} {I : Set i} {R : Set r} {n} →
         (I → R) → Op₂ R → {P′ : Pred I ℓ} → Decidable P′ → R → Vec I n → R
  fold {I = I} {R} f _∙_ p = foldr (λ _ → R) g
    where
      g : I → R → R
      g i acc with p i
      ... | yes _ = f i ∙ acc
      ... | no  _ = acc

  prod : ∀ {i ℓ} {I : Set i} {n} →
         (I → ℕ) → {P′ : Pred I ℓ} → Decidable P′ → Vec I n → ℕ
  prod f p = fold f _*_ p 1

  sum : ∀ {i ℓ} {I : Set i} {n} →
        (I → ℕ) → {P′ : Pred I ℓ} → Decidable P′ → Vec I n → ℕ
  sum f p = fold f _+_ p 0

  syntax sum (λ x → e) p v = Σ[ x ← v ∣ p $ e ]

  sumAll : ∀ {i} {I : Set i} {n} →
           (I → ℕ) → Vec I n → ℕ
  sumAll f = sum f {const ⊤} (const $ yes tt)

  syntax sumAll (λ x → e) v = Σ[ x ← v $ e ]

  fromZeroℕ : (n : ℕ) → Vec ℕ n
  fromZeroℕ zero    = []
  fromZeroℕ (suc n) = zero ∷ map suc (fromZeroℕ n)

  fromZeroFin : (n : ℕ) → Vec (Fin n) n
  fromZeroFin zero = []
  fromZeroFin (suc n) = zero ∷ map suc (fromZeroFin n)

  module ListLemmas where

    open import Relation.Binary.PropositionalEquality

    postulate
      pickʳ-lemma : ∀ n → fromZeroℕ (suc n) ≡ fromZeroℕ n ∷ʳ n
{-
    pickʳ-lemma : ∀ n → 0… (suc n) ≡ 0… n ∷ʳ n
    pickʳ-lemma zero = refl
    pickʳ-lemma (suc n) = {!!}
-}

  module FoldLemmas
         {i r ℓ} {I : Set i} {R : Set r}
         (f : I → R) (_∙_ : Op₂ R) {P′ : Pred I ℓ}
         (P : Decidable P′) (ε : R) where

    open ListLemmas

    open import Relation.Binary.PropositionalEquality

    empty-lemma : ∀ {n} (is : Vec I n) → Empty P′ → fold f _∙_ P ε is ≡ ε
    empty-lemma []       e = refl
    empty-lemma (i ∷ is) e with P i
    ... | yes p = ⊥-elim (e i p)
    ... | no ¬p = empty-lemma is e

    ∈ˡ-lemma : ∀ {n} (i : I) (is : Vec I n) →
               i ∈ P′ → fold f _∙_ P ε (i ∷ is) ≡ f i ∙ fold f _∙_ P ε is
    ∈ˡ-lemma i is i∈P′ with P i
    ... | yes p = refl
    ... | no ¬p = ⊥-elim (¬p i∈P′)

    ∉ˡ-lemma : ∀ {n} (i : I) (is : Vec I n) →
               i ∉ P′ → fold f _∙_ P ε (i ∷ is) ≡ fold f _∙_ P ε is
    ∉ˡ-lemma i is i∉P′ with P i
    ... | yes p = ⊥-elim (i∉P′ p)
    ... | no ¬p = refl

    ∈ʳ-lemma : ∀ {n} (is : Vec I n) (i : I) → Associative _≡_ _∙_ → Commutative _≡_ _∙_ →
               i ∈ P′ → fold f _∙_ P ε (is ∷ʳ i) ≡ fold f _∙_ P ε is ∙ f i
    ∈ʳ-lemma [] i assoc comm i∈P′ with P i
    ... | yes p = comm (f i) ε
    ... | no ¬p = ⊥-elim (¬p i∈P′)
    ∈ʳ-lemma (i ∷ is) i′ assoc comm i∈P′ with P i′ | P i
    ... | yes p | yes p′ =
      begin
        f i ∙ fold f _∙_ P ε (is ∷ʳ i′)
          ≡⟨ cong (_∙_ (f i)) (∈ʳ-lemma is i′ assoc comm i∈P′) ⟩
        f i ∙ (fold f _∙_ P ε is ∙ f i′)
          ≡⟨ sym (assoc (f i) (fold f _∙_ P ε is) (f i′)) ⟩
        (f i ∙ fold f _∙_ P ε is) ∙ f i′
      ∎
      where
        open ≡-Reasoning
    ... | yes p | no ¬p′ = ∈ʳ-lemma is i′ assoc comm i∈P′
    ... | no ¬p | _ = ⊥-elim (¬p i∈P′)

  module PQFoldLemmas
         {i r ℓ} {I : Set i} {R : Set r} (f : I → R) (_∙_ : Op₂ R)
         {P′ : Pred I ℓ} (P : Decidable P′)
         {Q′ : Pred I ℓ} (Q : Decidable Q′) (ε : R) where

    open import Relation.Binary.PropositionalEquality

    pq-lemma : ∀ {n} (is : Vec I n) →
               P′ ⊆ Q′ → P′ ⊇ Q′ → fold f _∙_ P ε is ≡ fold f _∙_ Q ε is
    pq-lemma []       _   _   = refl
    pq-lemma (i ∷ is) P⊆Q P⊇Q with P i | Q i
    ... | yes p | yes q = cong (_∙_ (f i)) (pq-lemma is P⊆Q P⊇Q)
    ... | no ¬p | no ¬q = pq-lemma is P⊆Q P⊇Q
    ... | yes p | no ¬q = ⊥-elim (¬q (P⊆Q p))
    ... | no ¬p | yes q = ⊥-elim (¬p (P⊇Q q))


  module MonoidFoldLemmas
         {i r ℓ₁ ℓ₂} {I : Set i} (M : Monoid r ℓ₁)
         (f : I → Monoid.Carrier M)
         {P′ : Pred I ℓ₂} (P : Decidable P′) where

    open Monoid M renaming (Carrier to R)

    ∈ʳ-lemma : ∀ {n} (is : Vec I n) (i : I) →
               i ∈ P′ → fold f _∙_ P ε (is ∷ʳ i) ≈ fold f _∙_ P ε is ∙ f i
    ∈ʳ-lemma [] i i∈P′ with P i
    ... | yes p =
      begin
        f i ∙ ε                           ≈⟨ proj₂ identity $ f i ⟩
        f i                               ≈⟨ sym $ proj₁ identity $ f i ⟩
        ε ∙ f i
      ∎
      where open EqR setoid
    ... | no ¬p = ⊥-elim (¬p i∈P′)
    ∈ʳ-lemma (i ∷ is) i′ i∈P′ with P i′ | P i
    ... | yes p | yes p′ =
      begin
        f i ∙ fold f _∙_ P ε (is ∷ʳ i′)   ≈⟨ ∙-cong refl (∈ʳ-lemma is i′ i∈P′) ⟩
        f i ∙ (fold f _∙_ P ε is ∙ f i′)  ≈⟨ sym (assoc (f i) (fold f _∙_ P ε is) (f i′)) ⟩
        (f i ∙ fold f _∙_ P ε is) ∙ f i′
      ∎
      where open EqR setoid
    ... | yes p | no ¬p′ = ∈ʳ-lemma is i′ i∈P′
    ... | no ¬p | _ = ⊥-elim (¬p i∈P′)


  module SumFoldLemmas
         {ℓ} (f : ℕ → ℕ) {P′ : Pred ℕ ℓ} (P : Decidable P′) where

    open import Data.Nat.Properties using (commutativeSemiring)
    open import Algebra using (CommutativeSemiring)
    open CommutativeSemiring commutativeSemiring hiding (_+_; _*_)

    open MonoidFoldLemmas +-monoid id (const $ yes tt)
    open ListLemmas

    open Monoid +-monoid using (identity)

--    suc-lemma : ∀ {n} → sumAll (f ∘ suc) (0… n) ≈ sumAll f (0… n) +

    postulate
      last-lemma : ∀ {n} → sumAll f (fromZeroℕ (suc n)) ≈ sumAll f (fromZeroℕ n) + f n

--    last-lemma : ∀ {n} → sumAll f (0… (suc n)) ≈ sumAll f (0… n) + f n
--    last-lemma {zero} = proj₂ identity (f zero)
--    last-lemma {n} = {!sumAll f (0 ∷ map suc (0… n))!}
