open import Algebra

module Bigop.Properties.CommutativeMonoid
       {c ℓ} (M : CommutativeMonoid c ℓ) where

open import Bigop.Core
-- open import Bigop.Filter
import Bigop.Properties.Monoid as MonoidProps

open import Data.List.Base
open import Data.Product hiding (map; swap)
open import Function
open import Relation.Nullary
open import Relation.Unary

open CommutativeMonoid M renaming (Carrier to R; identity to ident)
open MonoidProps {c} {ℓ} monoid public

open import Relation.Binary.EqReasoning setoid
open Fold monoid

{-
perm : (f : I → R) (is : List I) → fold f is ≈ fold f (reverse is)
perm f []       = refl
perm f (i ∷ is) = begin
  f i ∙ fold f is
    ≈⟨ comm _ _ ⟩
  fold f is ∙ f i
    ≈⟨ ∙-cong (perm f is) refl ⟩
  fold f (reverse is) ∙ f i
    ≈⟨ sym (last f i (reverse is)) ⟩
  fold f (reverse is ∷ʳ i)
    ≈⟨ cong″ (λ x → refl) (P.sym (reverse-∷ʳ i is)) ⟩ -- ≡⟨ P.cong (fold f) (P.sym (reverse-∷ʳ i is)) ⟩
  fold f (reverse (i ∷ is)) ∎
  where
    import Relation.Binary.PropositionalEquality as P
    open P.≡-Reasoning renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
{-
    reverse′ : ∀ {a} {A : Set a} → List A → List A
    reverse′ [] = []
    reverse′ (x ∷ xs) = reverse′ xs ∷ʳ x

    reverse-reverse′ : ∀ {a} {A : Set a} (xs : List A) → reverse xs P.≡ reverse′ xs
    reverse-reverse′ [] = P.refl
    reverse-reverse′ (x ∷ xs) = start
      foldl (λ rev x → x ∷ rev) (x ∷ []) xs
        ≣⟨ {!reverse (x ∷ xs)!} ⟩
      reverse xs ++ [ x ]
        ≣⟨ P.cong₂ _++_ (reverse-reverse′ xs) P.refl ⟩
      reverse′ xs ∷ʳ x □
-}
    reverse-∷ʳ : ∀ (i : I) is → reverse (i ∷ is) P.≡ reverse is ∷ʳ i
    reverse-∷ʳ i []       = P.refl
    reverse-∷ʳ i (j ∷ js) = start
      reverse (i ∷ j ∷ js)
        ≣⟨ {!reverse (i ∷ j ∷ js)!} ⟩
      reverse (j ∷ js) ∷ʳ i □
-}

split : ∀ {i} {I : Set i} (f g : I → R) (is : List I) →
         fold f is ∙ fold g is ≈ fold (λ i → f i ∙ g i) is
       -- Σ[ k ← is $ f k ] + Σ[ k ← is $ g k ] ≡ Σ[ k ← is $ f k + g k ]
split f g [] = proj₁ ident _
split f g (i ∷ is) = begin
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
        ≈⟨ (refl {g i}) ⟨ ∙-cong ⟩ split f g is ⟩
      g i ∙ fold (λ i → f i ∙ g i) is ∎

swap : ∀ {i j} {I : Set i} {J : Set j} (f : J → I → R)
         (js : List J) (is : List I) →
         fold (λ j → fold (f j) is) js ≈ fold (λ i → fold (flip f i) js) is
swap f [] ys = sym (identity ys)
swap f xs [] = identity xs
swap f (x ∷ xs) ys = begin
  fold (f x) ys ∙ fold (λ j → fold (f j) ys) xs
    ≈⟨ refl {fold (f x) ys} ⟨ ∙-cong ⟩ swap f xs ys ⟩
  fold (f x) ys ∙ fold (λ i → fold (flip f i) xs) ys
    ≈⟨ split (f x) (λ i → fold (flip f i) xs) ys ⟩
  fold (λ i → f x i ∙ fold (flip f i) xs) ys ∎

open import Bigop.Filter using (_∥_; ∁-dec)

postulate
  split-P : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → (f : I → R) (is : List I)
            (p : Decidable P) →
            fold f is ≈ fold f (is ∥ p) ∙ fold f (is ∥ ∁-dec p)

{-
split-P : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → (f : I → R) (is : List I)
          (p : Decidable P) →
          fold f is ≈ fold f (is ∥ p) ∙ fold f (is ∥ ∁-dec p)
split-P f [] p = sym (proj₁ ident _)
split-P f (i ∷ is) p with p i
split-P {ℓ = ℓ} {P = P} f (i ∷ is) p | yes pi = begin
  f i ∙ fold f is
    ≈⟨ {!!} ⟩
  fold f (_∥_ {ℓ = ℓ} {P = P} (i ∷ is) {!p!}) ∙ fold f (_∥_ {ℓ = ℓ} {P = P} (i ∷ is) {!∁-dec p!}) ∎
split-P {ℓ = ℓ} {P = P} f (i ∷ is) p | no ¬pi = begin
  f i ∙ fold f is
    ≈⟨ {!!} ⟩
  fold f (_∥_ {ℓ = ℓ} {P = P} (i ∷ is) {!p!}) ∙ fold f (_∥_ {ℓ = ℓ} {P = ∁ P} (i ∷ is) (∁-dec {!p!})) ∎
-}
