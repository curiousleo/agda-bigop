open import Algebra

module Bigop.SubsetCore
    {c ℓ} (cmon : CommutativeMonoid c ℓ)
    where

open import Data.Fin hiding (fold; fold′)
open import Data.Fin.Subset
open import Data.Nat hiding (fold)
open import Data.Product hiding (map; zip)
open import Data.Vec hiding (_∈_)

open import Function using (_∘_; id)

open CommutativeMonoid cmon

fold′ : ∀ {n} → (Fin n → Carrier) → Subset n → Carrier
fold′ f []             = ε
fold′ f (inside  ∷ xs) = f zero ∙ fold′ (f ∘ suc) xs
fold′ f (outside ∷ xs) =          fold′ (f ∘ suc) xs

infix 6 ⨁-syntax

⨁-syntax = fold′
syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v ] e

open import Algebra.FunctionProperties _≈_

open import Relation.Binary.EqReasoning setoid
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

fold-⊥ : ∀ {n} f → fold′ f (⊥ {n}) ≈ ε
fold-⊥ {zero}  f = refl
fold-⊥ {suc n} f = fold-⊥ (f ∘ suc)

fold-∪ : ∀ {n} (idp : Idempotent _∙_) f (xs : Subset n) (ys : Subset n) → fold′ f (xs ∪ ys) ≈ fold′ f xs ∙ fold′ f ys
fold-∪ idp f []             []       = sym (proj₁ identity _)
fold-∪ idp f (inside ∷ xs) (inside  ∷ ys) =
  begin
    f zero ∙ fold′ (f ∘ suc) (xs ∪ ys)
      ≈⟨ ∙-cong (sym (idp _)) (fold-∪ idp (f ∘ suc) xs ys) ⟩
    (f zero ∙ f zero) ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys)
      ≈⟨ assoc _ _ _ ⟩
    f zero ∙ (f zero ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys))
      ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    f zero ∙ ((f zero ∙ fold′ (f ∘ suc) xs) ∙ fold′ (f ∘ suc) ys)
      ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
    f zero ∙ ((fold′ (f ∘ suc) xs ∙ f zero) ∙ fold′ (f ∘ suc) ys)
      ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
    f zero ∙ (fold′ (f ∘ suc) xs ∙ (f zero ∙ fold′ (f ∘ suc) ys))
      ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ fold′ (f ∘ suc) xs) ∙ (f zero ∙ fold′ (f ∘ suc) ys)
  ∎
fold-∪ idp f (inside ∷ xs) (outside ∷ ys) =
  begin
    f zero ∙ fold′ (f ∘ suc) (xs ∪ ys)
      ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
    f zero ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys)
      ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ fold′ (f ∘ suc) xs) ∙ fold′ (f ∘ suc) ys
  ∎
fold-∪ idp f (outside ∷ xs) (inside  ∷ ys) =
  begin
    f zero ∙ fold′ (f ∘ suc) (xs ∪ ys)
      ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
    f zero ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys)
      ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ fold′ (f ∘ suc) xs) ∙ fold′ (f ∘ suc) ys
      ≈⟨ ∙-cong (comm _ _) refl ⟩
    (fold′ (f ∘ suc) xs ∙ f zero) ∙ fold′ (f ∘ suc) ys
      ≈⟨ assoc _ _ _ ⟩
    fold′ (f ∘ suc) xs ∙ (f zero ∙ fold′ (f ∘ suc) ys)
  ∎
fold-∪ idp f (outside ∷ xs) (outside ∷ ys) = fold-∪ idp (f ∘ suc) xs ys

fold-⁅i⁆ : ∀ {n} f (i : Fin n) → fold′ f ⁅ i ⁆ ≈ f i
fold-⁅i⁆ f zero =
  begin
    f zero ∙ fold′ (f ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ (f ∘ suc)) ⟩
    f zero ∙ ε                  ≈⟨ proj₂ identity _ ⟩
    f zero
  ∎
fold-⁅i⁆ f (suc i) = fold-⁅i⁆ (f ∘ suc) i

fold-cong-lemma : ∀ {n} (f g : Fin (suc n) → Carrier) x (xs : Subset n) →
                  (∀ i → i ∈ (x ∷ xs) → f i ≈ g i) → (∀ i → i ∈ xs → f (suc i) ≈ g (suc i))
fold-cong-lemma f g x [] eq i ()
fold-cong-lemma f g x (inside ∷ ys) eq i i∈y∷ys = eq (suc i) (there i∈y∷ys)
fold-cong-lemma f g x (outside ∷ ys) eq zero ()
fold-cong-lemma f g x (outside ∷ ys) eq (suc i) (there i∈y∷ys) = fold-cong-lemma (f ∘ suc) (g ∘ suc) outside ys (λ i x → eq (suc i) (there x)) i i∈y∷ys

fold-cong : ∀ {n} f g (xs : Subset n) → (∀ i → i ∈ xs → f i ≈ g i) → fold′ f xs ≈ fold′ g xs
fold-cong f g []             eq = refl
fold-cong f g (inside  ∷ xs) eq = ∙-cong (eq zero here) (fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g inside xs eq))
fold-cong f g (outside ∷ xs) eq = fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g outside xs eq)
