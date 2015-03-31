{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Prototypes.BigopFold where

  import Relation.Binary.EqReasoning as EqR

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core using (Op₂)

  open import Data.Product hiding (map; Σ-syntax)
  open import Data.Fin hiding (_+_; _≤_; fold; fold′)
  open import Data.Nat hiding (fold) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
  open import Data.List.Base

  open import Function

  module Core {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

    open Monoid M renaming (Carrier to R)

    fold : (I → R) → List I → R
    fold f = foldr (λ x y → (f x) ∙ y) ε

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

  range : ∀ {from to} → from ≤ to → List (Fin to)
  range (z≤n {zero})          = []
  range (z≤n {suc to})        = zero ∷ map suc (range (z≤n {to}))
  range (s≤s {from} {to} f≤t) = map suc (range f≤t)

  fromLenF : (from len : ℕ) → List (Fin (from +ℕ len))
  fromLenF from len = range {from} {from + len} (m≤m+n from len)
    where
      open Data.Nat
      open import Data.Nat.Properties.Simple

      ≤-refl : ∀ n → n ≤ n
      ≤-refl zero    = z≤n
      ≤-refl (suc n) = s≤s (≤-refl n)

      m≤m+n : ∀ m n → m ≤ m + n
      m≤m+n zero n = z≤n
      m≤m+n (suc m) zero rewrite +-comm (suc m) zero = ≤-refl (suc m)
      m≤m+n (suc m) (suc n) = s≤s (m≤m+n m (suc n))

  fromLenℕ : (from len : ℕ) → List ℕ
  fromLenℕ from to = map toℕ (fromLenF from to)

  fromLenℕ′ : ℕ → ℕ → List ℕ
  fromLenℕ′ from zero = []
  fromLenℕ′ from (suc len) = from ∷ fromLenℕ′ (suc from) len

  module RangeLemmas where
    open import Relation.Binary.PropositionalEquality
    open import Data.Nat.Base
    open import Data.Nat.Properties.Simple

    open ≡-Reasoning

    suc-lemma : ∀ m n → map suc (fromLenℕ′ m n) ≡ fromLenℕ′ (suc m) n
    suc-lemma m zero    = refl
    suc-lemma m (suc n) = cong (_∷_ (suc m)) (suc-lemma (suc m) n)

    suc-head-lemma : ∀ m n → m ∷ (fromLenℕ′ (suc m) n) ≡ fromLenℕ′ m (suc n)
    suc-head-lemma m n = refl

    suc-last-lemma : ∀ m n → fromLenℕ′ m (suc n) ≡ (fromLenℕ′ m n) ∷ʳ (m + n)
    suc-last-lemma m zero = cong (_∷ʳ_ []) $ +-comm zero m
    suc-last-lemma m (suc n) = begin
      m ∷ fromLenℕ′ (suc m) (suc n)
        ≡⟨ cong (_∷_ m) $ suc-last-lemma (suc m) n ⟩
      m ∷ (fromLenℕ′ (suc m) n) ∷ʳ suc m + n
        ≡⟨ cong (_∷ʳ_ $ fromLenℕ′ m (suc n)) $ sym $ +-suc m n ⟩
      fromLenℕ′ m (suc n) ∷ʳ m + suc n ∎

  module _ where
    open import Relation.Binary.PropositionalEquality

    _…+_ = fromLenℕ′

    test : 2 …+ 3 ≡ 2 ∷ 3 ∷ 4 ∷ []
    test = refl

  module MonoidLemmas
         {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

    open Monoid M renaming (Carrier to R)
    open EqR setoid

    open Core M

    Σ-head : (f : I → R) (x : I) (xs : List I) →
             fold f (x ∷ xs) ≈ f x ∙ fold f xs
    Σ-head _ _ _ = refl

    Σ-last : (f : I → R) (x : I) (xs : List I) →
             fold f (xs ∷ʳ x) ≈ fold f xs ∙ f x
    Σ-last f x [] = begin
      f x ∙ ε  ≈⟨ proj₂ identity _ ⟩
      f x      ≈⟨ sym $ proj₁ identity _ ⟩
      ε ∙ f x  ∎
    Σ-last f x (y ∷ ys) = begin
      f y ∙ fold f (ys ∷ʳ x)   ≈⟨ ∙-cong refl (Σ-last f x ys) ⟩
      f y ∙ (fold f ys ∙ f x)  ≈⟨ sym $ assoc _ _ _ ⟩
      (f y ∙ fold f ys) ∙ f x  ∎

    Σ-shift : (f : I → R) (x : I) (xs : List I) →
              f x ≈ ε → fold f (x ∷ xs) ≈ fold f xs
    Σ-shift f x xs fx≈ε = begin
      f x ∙ fold f xs  ≈⟨ ∙-cong fx≈ε refl ⟩
      ε ∙ fold f xs    ≈⟨ proj₁ identity _ ⟩
      fold f xs        ∎

    Σ-zero : (xs : List I) → fold (const ε) xs ≈ ε
    Σ-zero [] = refl
    Σ-zero (x ∷ xs) = trans (proj₁ identity _) (Σ-zero xs)

    Σ-cong′ : {f g : I → R} → (∀ x → f x ≈ g x) → (is : List I) →
              fold f is ≈ fold g is
    Σ-cong′         f≗g []       = refl
    Σ-cong′ {f} {g} f≗g (i ∷ is) = begin
      f i ∙ fold f is
        ≈⟨ f≗g i ⟨ ∙-cong ⟩ Σ-cong′ {f} {g} f≗g is ⟩
      g i ∙ fold g is ∎

    -- Σ-cong could be generalised further to f : I → R, g : J → R, h : I → J
    Σ-cong : {f g : I → R} (h : I → I) → (∀ x → f x ≈ g (h x)) → (is : List I) →
             fold f is ≈ fold g (map h is)
    Σ-cong         h f≗gh []       = refl
    Σ-cong {f} {g} h f≗gh (i ∷ is) = begin
      f i ∙ fold f is
        ≈⟨ f≗gh i ⟨ ∙-cong ⟩ Σ-cong {f} {g} h f≗gh is ⟩
      g (h i) ∙ fold g (map h is) ∎

  module CommutativeMonoidLemmas
         {c ℓ} (M : CommutativeMonoid c ℓ) {i} {I : Set i} {j} {J : Set j} where

    open CommutativeMonoid M renaming (Carrier to R)
    open EqR setoid

    open Core monoid

    open MonoidLemmas monoid

    Σ-lift : (f g : I → R) (is : List I) →
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

    Σ-swap : (f : J → I → R) (js : List J) (is : List I) →
             fold (λ j → fold (f j) is) js ≈ fold (λ i → fold (flip f i) js) is
    Σ-swap f [] ys = sym (Σ-zero ys)
    Σ-swap f xs [] = Σ-zero xs
    Σ-swap f (x ∷ xs) ys = begin
      fold (f x) ys ∙ fold (λ j → fold (f j) ys) xs
        ≈⟨ refl {fold (f x) ys} ⟨ ∙-cong ⟩ Σ-swap f xs ys ⟩
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

    Σ-distrˡ : (f : I → R) (x : R) (is : List I) →
               x * fold f is ≈ fold (λ k → x * (f k)) is
    Σ-distrˡ f x [] = proj₂ *-zero x
    Σ-distrˡ f x (n ∷ ns) =
      begin
        x * (f n + fold f ns)
          ≈⟨ proj₁ distrib x (f n) (fold f ns) ⟩
        (x * f n) + (x * fold f ns)
          ≈⟨ refl {x * f n} ⟨ +-cong ⟩ Σ-distrˡ f x ns ⟩
        (x * f n) + fold ((_*_ x) ∘ f) ns
      ∎
