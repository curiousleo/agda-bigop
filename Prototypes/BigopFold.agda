{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Prototypes.BigopFold where

  import Relation.Binary.EqReasoning as EqR

  open import Data.Product hiding (map; Σ-syntax)
  open import Data.Fin hiding (_+_; fold; fold′)
  open import Data.Nat hiding (fold) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
  open import Data.Vec hiding (_∈_; sum)

  open import Function

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core using (Op₂)

  module Core {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

    open Monoid M renaming (Carrier to R)

    fold : ∀ {n} → (I → R) → Vec I n → R
    fold f = foldr _ (λ x y → (f x) ∙ y) ε

    Σ-syntax : _
    Σ-syntax = fold

    syntax Σ-syntax (λ x → e) v = Σ[ x ← v $ e ]

    Π-syntax : _
    Π-syntax = fold

    syntax Π-syntax (λ x → e) v = Π[ x ← v $ e ]

    ⨁-syntax : _
    ⨁-syntax = fold

    syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v $ e ]

    ⨂-syntax : _
    ⨂-syntax = fold

    syntax ⨂-syntax (λ x → e) v = ⨂[ x ← v $ e ]

  fromZeroℕ : (n : ℕ) → Vec ℕ n
  fromZeroℕ zero    = []
  fromZeroℕ (suc n) = zero ∷ map suc (fromZeroℕ n)

  fromZeroFin : (n : ℕ) → Vec (Fin n) n
  fromZeroFin zero = []
  fromZeroFin (suc n) = zero ∷ map suc (fromZeroFin n)


  module MonoidLemmas
         {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

    open Monoid M renaming (Carrier to R)
    open EqR setoid

    open Core M

    Σ-head : ∀ {n} → (f : I → R) (x : I) (xs : Vec I n) →
             fold f (x ∷ xs) ≈ f x ∙ fold f xs
    Σ-head _ _ _ = refl

    Σ-shift : ∀ {n} → (f : I → R) (x : I) (xs : Vec I n) →
              f x ≈ ε → fold f (x ∷ xs) ≈ fold f xs
    Σ-shift f x xs fx≈ε = begin
      f x ∙ fold f xs  ≈⟨ ∙-cong fx≈ε refl ⟩
      ε ∙ fold f xs    ≈⟨ proj₁ identity _ ⟩
      fold f xs ∎

    Σ-zero : ∀ {n} (xs : Vec I n) → fold (const ε) xs ≈ ε
    Σ-zero [] = refl
    Σ-zero (x ∷ xs) = trans (proj₁ identity _) (Σ-zero xs)

    Σ-cong : ∀ {n} {f g : I → R} →
             (∀ x → f x ≈ g x) → (is : Vec I n) →
             fold {n = n} f is ≈ fold g is
    Σ-cong             f≗g []       = refl
    Σ-cong {f = f} {g} f≗g (i ∷ is) = begin
      f i ∙ fold f is
        ≈⟨ f≗g i ⟨ ∙-cong ⟩ Σ-cong {f = f} {g} f≗g is ⟩
      g i ∙ fold g is ∎

  module CommutativeMonoidLemmas
         {c ℓ} (M : CommutativeMonoid c ℓ) {i} {I : Set i} {j} {J : Set j} where

    open CommutativeMonoid M renaming (Carrier to R)
    open EqR setoid

    open Core monoid

    open MonoidLemmas monoid

    Σ-lift : ∀ {n} (f g : I → R) (is : Vec I n) →
              fold f is ∙ fold g is ≈ fold (λ i → f i ∙ g i) is
    Σ-lift f g [] = proj₁ identity _
    Σ-lift f g (i ∷ is) = begin
      (f i ∙ fold f is) ∙ (g i ∙ fold g is)
        ≈⟨ assoc (f i) (fold f is) (g i ∙ fold g is) ⟩
      f i ∙ (fold f is ∙ (g i ∙ fold g is))
        ≈⟨ refl {f i} ⟨ ∙-cong ⟩ lemma ⟩
      f i ∙ (g i ∙ fold (λ i → f i ∙ g i) is)
        ≈⟨ sym (assoc (f i) (g i) (fold (λ i → f i ∙ g i) is)) ⟩
      (f i ∙ g i) ∙ fold (λ i → f i ∙ g i) is ∎
      where
        lemma : fold f is ∙ (g i ∙ fold g is) ≈
                g i ∙ fold (λ i → f i ∙ g i) is
        lemma = begin
          fold f is ∙ (g i ∙ fold g is)
            ≈⟨ sym (assoc (fold f is) (g i) (fold g is)) ⟩
          (fold f is ∙ g i) ∙ fold g is
            ≈⟨ comm (fold f is) (g i) ⟨ ∙-cong ⟩ refl ⟩
          (g i ∙ fold f is) ∙ fold g is
            ≈⟨ assoc (g i) (fold f is) (fold g is) ⟩
          g i ∙ (fold f is ∙ fold g is)
            ≈⟨ (refl {g i}) ⟨ ∙-cong ⟩ Σ-lift f g is ⟩
          g i ∙ fold (λ i → f i ∙ g i) is ∎

    Σ-swap : ∀ {m n} → (f : J → I → R) (js : Vec J m) (is : Vec I n) →
             fold (λ j → fold (f j) is) js ≈ fold (λ i → fold (flip f i) js) is
    Σ-swap f [] ys = sym (Σ-zero ys)
    Σ-swap f xs [] = Σ-zero xs
    Σ-swap {suc m} {n} f (x ∷ xs) ys = begin
      fold (f x) ys ∙ fold (λ j → fold (f j) ys) xs
        ≈⟨ refl {fold (f x) ys} ⟨ ∙-cong ⟩ Σ-swap {m} {n} f xs ys ⟩
      fold (f x) ys ∙ fold (λ i → fold (flip f i) xs) ys
        ≈⟨ Σ-lift (f x) (λ i → fold (flip f i) xs) ys ⟩
      fold (λ i → f x i ∙ fold (flip f i) xs) ys ∎


  module SemiringWithoutOneLemmas
         {c ℓ} (S : SemiringWithoutOne c ℓ) {i} {I : Set i} where

    open SemiringWithoutOne S
      renaming (Carrier to R; zero to *-zero)
    open EqR setoid

    open Core +-monoid

    open CommutativeMonoidLemmas +-commutativeMonoid {I = I}

    Σ-distrˡ : ∀ {m} (f : I → R) (x : R) (is : Vec I m) →
              x * fold f is ≈ fold ((_*_ x) ∘ f) is
    Σ-distrˡ f x [] = proj₂ *-zero x
    Σ-distrˡ {suc m} f x (n ∷ ns) =
      begin
        x * (f n + fold f ns)
          ≈⟨ proj₁ distrib x (f n) (fold f ns) ⟩
        (x * f n) + (x * fold f ns)
          ≈⟨ refl {x * f n} ⟨ +-cong ⟩ Σ-distrˡ {m} f x ns ⟩
        (x * f n) + fold ((_*_ x) ∘ f) ns
      ∎
