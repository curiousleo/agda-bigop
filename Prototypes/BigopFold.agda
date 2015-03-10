{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Prototypes.BigopFold where

  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary hiding (Decidable)
  import Relation.Binary.EqReasoning as EqR
  import Relation.Binary.PropositionalEquality as P

  open import Data.Empty
  open import Data.Bool
  import Data.List as L
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
  open import Algebra.FunctionProperties.Core using (Op₂)

  filter : ∀ {a} {A : Set a} {n} (p : A → Bool) (xs : Vec A n) →
           Vec A (L.length (L.filter p (toList xs)))
  filter p xs = fromList $ L.filter p $ toList xs

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

    postulate
      pickʳ-lemma : ∀ n → fromZeroℕ (suc n) P.≡ fromZeroℕ n ∷ʳ n
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
    open import Algebra.FunctionProperties {A = R} (_≡_)

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

    ∈ʳ-lemma : ∀ {n} (is : Vec I n) (i : I) → Associative _∙_ → Commutative _∙_ →
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

    pq-lemma : ∀ {n} (is : Vec I n) →
               P′ ⊆ Q′ → P′ ⊇ Q′ → fold f _∙_ P ε is P.≡ fold f _∙_ Q ε is
    pq-lemma []       _   _   = P.refl
    pq-lemma (i ∷ is) P⊆Q P⊇Q with P i | Q i
    ... | yes p | yes q = P.cong (_∙_ (f i)) (pq-lemma is P⊆Q P⊇Q)
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
         {ℓ} {P′ : Pred ℕ ℓ} (P : Decidable P′) where

    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring
      using (+-isCommutativeMonoid; setoid; distrib;
             _≈_; refl; sym; trans)
      renaming (zero to *-zero) public

    open IsCommutativeMonoid +-isCommutativeMonoid
      using ()
      renaming (∙-cong to +-cong; assoc to +-assoc; comm to +-comm) public

    open EqR setoid

    postulate
      distribˡ-lemma : ∀ {m i} {I : Set i} (f : I → ℕ) (x : ℕ) (ns : Vec I m) →
                       x * sumAll f ns ≈ sumAll ((_*_ x) ∘ f) ns

{-
    filter-lemma : ∀ {ℓ i} {I : Set i} {n} (f : I → ℕ) (is : Vec I n)
                   {P′ : Pred I ℓ} (P : Decidable P′) →
                   sum f P is ≈ sumAll f (filter (λ i → ⌊ P i ⌋) is)
    filter-lemma f [] P = P.refl
    filter-lemma {ℓ} {I = I} {suc n} f (i ∷ is) P with P i
    ... | yes p = +-cong refl (filter-lemma {ℓ} {I = I} {n} f is P)
    ... | no ¬p = filter-lemma f is P
-}

    Σ-cong : ∀ {i} {I : Set i} {n} (f g : I → ℕ) →
             (∀ x → f x ≈ g x) → (is : Vec I n) →
             sumAll {n = n} f is ≈ sumAll g is
    Σ-cong f g f≗g []       = refl
    Σ-cong f g f≗g (i ∷ is) = begin
      f i + sumAll f is
        ≈⟨ f≗g i ⟨ +-cong ⟩ Σ-cong f g f≗g is ⟩
      g i + sumAll g is ∎

    Σ-zero : ∀ {n} {i} {I : Set i} (xs : Vec I n) → sumAll (const 0) xs ≈ 0
    Σ-zero [] = refl
    Σ-zero (x ∷ xs) = Σ-zero xs

    Σ-distr : ∀ {n} {i} {I : Set i} (f g : I → ℕ) (is : Vec I n) →
              sumAll f is + sumAll g is ≈ sumAll (λ i → f i + g i) is
    Σ-distr f g [] = refl
    Σ-distr f g (i ∷ is) = begin
      (f i + sumAll f is) + (g i + sumAll g is)
        ≈⟨ +-assoc (f i) (sumAll f is) (g i + sumAll g is) ⟩
      f i + (sumAll f is + (g i + sumAll g is))
        ≈⟨ refl {f i} ⟨ +-cong ⟩ lemma ⟩
      f i + (g i + sumAll (λ i → f i + g i) is)
        ≈⟨ sym (+-assoc (f i) (g i) (sumAll (λ i → f i + g i) is)) ⟩
      (f i + g i) + sumAll (λ i → f i + g i) is ∎
      where
        lemma : sumAll f is + (g i + sumAll g is) ≈
                g i + sumAll (λ i → f i + g i) is
        lemma = begin
          sumAll f is + (g i + sumAll g is)
            ≈⟨ sym (+-assoc (sumAll f is) (g i) (sumAll g is)) ⟩
          (sumAll f is + g i) + sumAll g is
            ≈⟨ +-comm (sumAll f is) (g i) ⟨ +-cong ⟩ refl ⟩
          (g i + sumAll f is) + sumAll g is
            ≈⟨ +-assoc (g i) (sumAll f is) (sumAll g is) ⟩
          g i + (sumAll f is + sumAll g is)
            ≈⟨ (refl {g i}) ⟨ +-cong ⟩ Σ-distr f g is ⟩
          g i + sumAll (λ i → f i + g i) is ∎

    Σ-swap : ∀ {m n} {i} {I : Set i} →
             (f : I → I → ℕ) (xs : Vec I m) (ys : Vec I n) →
             sumAll (λ j → sumAll (flip f j) ys) xs ≈
             sumAll {n = n} (λ i → sumAll (f i) xs) ys
    Σ-swap f [] ys = sym (Σ-zero ys)
    Σ-swap f xs [] = Σ-zero xs
    Σ-swap {suc m} {n} {I = I} f (x ∷ xs) ys = begin
      sumAll (flip f x) ys + sumAll (λ j → sumAll (flip f j) ys) xs
        ≈⟨ refl {sumAll (flip f x) ys} ⟨ +-cong ⟩ Σ-swap {m} {n} f xs ys ⟩
      sumAll (flip f x) ys + sumAll (λ i → sumAll (f i) xs) ys
        ≈⟨ Σ-distr (flip f x) (λ i → sumAll (f i) xs) ys ⟩
      sumAll (λ i → f i x + sumAll (f i) xs) ys ∎

{-
    distribˡ-lemma : ∀ {m} (x : ℕ) (ns : Vec ℕ m) →
                     x * sumAll f ns ≈ sumAll ((_*_ x) ∘ f) ns
    distribˡ-lemma x [] = proj₂ *-zero x
    distribˡ-lemma {suc m} x (n ∷ ns) =
      begin
        x * (f n + sumAll f ns)
          ≈⟨ proj₁ distrib x (f n) (sumAll f ns) ⟩
        (x * f n) + (x * sumAll f ns)
          ≈⟨ refl ⟨ +-cong ⟩ distribˡ-lemma {m} x ns ⟩
        (x * f n) + sumAll ((_*_ x) ∘ f) ns
      ∎
      where
        open EqR setoid
-}
