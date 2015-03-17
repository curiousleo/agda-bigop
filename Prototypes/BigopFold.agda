{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Prototypes.BigopFold where

  import Relation.Binary.EqReasoning as EqR

  open import Data.Product hiding (map)
  open import Data.Fin hiding (_+_; fold; fold′)
  open import Data.Nat hiding (fold)
  open import Data.Vec hiding (_∈_; sum)

  open import Function

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core using (Op₂)

  fold : ∀ {i r} {I : Set i} {R : Set r} {n} →
         (I → R) → Op₂ R → R → Vec I n → R
  fold f _∙_ = foldr _ (λ x y → (f x) ∙ y)

  prod : ∀ {i} {I : Set i} {n} → (I → ℕ) → Vec I n → ℕ
  prod f = fold f _*_ 1

  sum : ∀ {i} {I : Set i} {n} → (I → ℕ) → Vec I n → ℕ
  sum f = fold f _+_ 0

  syntax sum (λ x → e) v = Σ[ x ← v $ e ]

  fromZeroℕ : (n : ℕ) → Vec ℕ n
  fromZeroℕ zero    = []
  fromZeroℕ (suc n) = zero ∷ map suc (fromZeroℕ n)

  fromZeroFin : (n : ℕ) → Vec (Fin n) n
  fromZeroFin zero = []
  fromZeroFin (suc n) = zero ∷ map suc (fromZeroFin n)

  module SumFoldLemmas where

    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring
      using (+-isCommutativeMonoid; setoid; distrib;
             _≈_; refl; sym; trans)
      renaming (zero to *-zero) public

    open IsCommutativeMonoid +-isCommutativeMonoid
      using ()
      renaming (∙-cong to +-cong; assoc to +-assoc; comm to +-comm) public

    open EqR setoid

    Σ-cong : ∀ {i} {I : Set i} {n} {f g : I → ℕ} →
             (∀ x → f x ≈ g x) → (is : Vec I n) →
             sum {n = n} f is ≈ sum g is
    Σ-cong             f≗g []       = refl
    Σ-cong {f = f} {g} f≗g (i ∷ is) = begin
      f i + sum f is
        ≈⟨ f≗g i ⟨ +-cong ⟩ Σ-cong {f = f} {g} f≗g is ⟩
      g i + sum g is ∎

    Σ-zero : ∀ {n} {i} {I : Set i} (xs : Vec I n) → sum (const 0) xs ≈ 0
    Σ-zero [] = refl
    Σ-zero (x ∷ xs) = Σ-zero xs

    Σ-lift : ∀ {n} {i} {I : Set i} (f g : I → ℕ) (is : Vec I n) →
              sum f is + sum g is ≈ sum (λ i → f i + g i) is
    Σ-lift f g [] = refl
    Σ-lift f g (i ∷ is) = begin
      (f i + sum f is) + (g i + sum g is)
        ≈⟨ +-assoc (f i) (sum f is) (g i + sum g is) ⟩
      f i + (sum f is + (g i + sum g is))
        ≈⟨ refl {f i} ⟨ +-cong ⟩ lemma ⟩
      f i + (g i + sum (λ i → f i + g i) is)
        ≈⟨ sym (+-assoc (f i) (g i) (sum (λ i → f i + g i) is)) ⟩
      (f i + g i) + sum (λ i → f i + g i) is ∎
      where
        lemma : sum f is + (g i + sum g is) ≈
                g i + sum (λ i → f i + g i) is
        lemma = begin
          sum f is + (g i + sum g is)
            ≈⟨ sym (+-assoc (sum f is) (g i) (sum g is)) ⟩
          (sum f is + g i) + sum g is
            ≈⟨ +-comm (sum f is) (g i) ⟨ +-cong ⟩ refl ⟩
          (g i + sum f is) + sum g is
            ≈⟨ +-assoc (g i) (sum f is) (sum g is) ⟩
          g i + (sum f is + sum g is)
            ≈⟨ (refl {g i}) ⟨ +-cong ⟩ Σ-lift f g is ⟩
          g i + sum (λ i → f i + g i) is ∎

    Σ-swap : ∀ {m n} {i j} {I : Set i} {J : Set j} →
             (f : J → I → ℕ) (xs : Vec J m) (ys : Vec I n) →
             sum (λ j → sum (f j) ys) xs ≈
             sum {n = n} (λ i → sum (flip f i) xs) ys
    Σ-swap f [] ys = sym (Σ-zero ys)
    Σ-swap f xs [] = Σ-zero xs
    Σ-swap {suc m} {n} {I = I} f (x ∷ xs) ys = begin
      sum (f x) ys + sum (λ j → sum (f j) ys) xs
        ≈⟨ refl {sum (f x) ys} ⟨ +-cong ⟩ Σ-swap {m} {n} f xs ys ⟩
      sum (f x) ys + sum (λ i → sum (flip f i) xs) ys
        ≈⟨ Σ-lift (f x) (λ i → sum (flip f i) xs) ys ⟩
      sum (λ i → f x i + sum (flip f i) xs) ys ∎

    Σ-distr : ∀ {m} {i} {I : Set i} (f : I → ℕ) (x : ℕ) (is : Vec I m) →
              x * sum f is ≈ sum ((_*_ x) ∘ f) is
    Σ-distr f x [] = proj₂ *-zero x
    Σ-distr {suc m} f x (n ∷ ns) =
      begin
        x * (f n + sum f ns)
          ≈⟨ proj₁ distrib x (f n) (sum f ns) ⟩
        (x * f n) + (x * sum f ns)
          ≈⟨ refl {x * f n} ⟨ +-cong ⟩ Σ-distr {m} f x ns ⟩
        (x * f n) + sum ((_*_ x) ∘ f) ns
      ∎
