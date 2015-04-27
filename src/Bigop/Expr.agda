open import Algebra

module Bigop.Expr {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

open import Data.Fin
import Data.Fin.Properties as Fin
open import Data.List.Base
open import Data.Maybe as Maybe
  using (Maybe; decToMaybe; From-just; from-just)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Vec using (Vec; lookup)
open import Function using (_∘_; _$_)
import Relation.Binary.EqReasoning
import Relation.Binary.List.Pointwise as Pointwise
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Reflection
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

open Monoid M
open Relation.Binary.EqReasoning setoid

data Expr (n : ℕ) : Set i where
  var  : Fin n → Expr n
  id   : Expr n
  _⊕_  : Expr n → Expr n → Expr n
  ⨁[_] : List I → (I → Expr n) → Expr n

Env : ℕ → Set _
Env n = Vec Carrier n

{-
private
  flatten : {n : ℕ} → Expr n → Vec Carrier n → List Carrier
  flatten (var x) ρ         = lookup x ρ ∷ []
  flatten id ρ              = []
  flatten (e₁ ⊕ e₂) ρ       = flatten e₁ ρ ++ flatten e₂ ρ
  flatten (⨁[ []     ] f) ρ = []
  flatten (⨁[ x ∷ xs ] f) ρ = flatten (f x) ρ ++ flatten (⨁[ xs ] f) ρ

⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
⟦ e ⟧ ρ = foldr _∙_ ε (flatten e ρ)
-}

⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
⟦ var n         ⟧ ρ = lookup n ρ
⟦ id            ⟧ ρ = ε
⟦ x ⊕ y         ⟧ ρ = ⟦ x ⟧ ρ ∙ ⟦ y ⟧ ρ
⟦ ⨁[ []     ] f ⟧ ρ = ε
⟦ ⨁[ x ∷ xs ] f ⟧ ρ = ⟦ f x ⟧ ρ ∙ ⟦ ⨁[ xs ] f ⟧ ρ

Normal : ℕ → Set
Normal n = List (Fin n)

⟦_⟧⇓ : ∀ {n} → Normal n → Env n → Carrier
⟦ []     ⟧⇓ ρ = ε
⟦ x ∷ xs ⟧⇓ ρ = lookup x ρ ∙ ⟦ xs ⟧⇓ ρ

normalise : ∀ {n} → Expr n → Normal n
normalise (var x)         = x ∷ []
normalise id              = []
normalise (e₁ ⊕ e₂)       = (normalise e₁) ++ (normalise e₂)
normalise (⨁[ []     ] f) = []
normalise (⨁[ x ∷ xs ] f) = normalise (f x) ++ normalise (⨁[ xs ] f)

homomorphic : ∀ {n} (nf₁ nf₂ : Normal n) (ρ : Env n) →
              ⟦ nf₁ ++ nf₂ ⟧⇓ ρ ≈ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)
homomorphic [] nf₂ ρ = begin
  ⟦ nf₂ ⟧⇓ ρ      ≈⟨ sym $ proj₁ identity _ ⟩
  ε ∙ ⟦ nf₂ ⟧⇓ ρ  ∎
homomorphic (x ∷ nf₁) nf₂ ρ = begin
  lookup x ρ ∙ ⟦ nf₁ ++ nf₂ ⟧⇓ ρ          ≈⟨ ∙-cong refl (homomorphic nf₁ nf₂ ρ) ⟩
  lookup x ρ ∙ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)  ≈⟨ sym $ assoc _ _ _ ⟩
  lookup x ρ ∙ ⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ    ∎

normalise-correct :
  ∀ {n} (e : Expr n) (ρ : Env n) → ⟦ normalise e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ
normalise-correct (var x) ρ = begin
  lookup x ρ ∙ ε  ≈⟨ proj₂ identity _ ⟩
  lookup x ρ      ∎
normalise-correct id ρ = begin
  ε  ∎
normalise-correct (e₁ ⊕ e₂) ρ = begin
  ⟦ normalise e₁ ++ normalise e₂ ⟧⇓ ρ        ≈⟨ homomorphic (normalise e₁) (normalise e₂) ρ ⟩
  ⟦ normalise e₁ ⟧⇓ ρ ∙ ⟦ normalise e₂ ⟧⇓ ρ  ≈⟨ ∙-cong (normalise-correct e₁ ρ) (normalise-correct e₂ ρ) ⟩
  ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ                        ∎
normalise-correct (⨁[ [] ] f) ρ = refl
normalise-correct (⨁[ x ∷ xs ] f) ρ = begin
  ⟦ normalise (f x) ++ normalise (⨁[ xs ] f) ⟧⇓ ρ
    ≈⟨ homomorphic (normalise (f x)) _ ρ ⟩
  ⟦ normalise (f x) ⟧⇓ ρ ∙ ⟦ normalise (⨁[ xs ] f) ⟧⇓ ρ
    ≈⟨ ∙-cong (normalise-correct (f x) ρ) (normalise-correct (⨁[ xs ] f) ρ) ⟩
  ⟦ f x ⟧ ρ ∙ ⟦ ⨁[ xs ] f ⟧ ρ ∎

open module R = Relation.Binary.Reflection
                  setoid var ⟦_⟧ (⟦_⟧⇓ ∘ normalise) normalise-correct
  public using (solve; _⊜_)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : ∀ {n} (nf₁ nf₂ : Normal n) → Dec (nf₁ ≡ nf₂)
nf₁ ≟ nf₂ = Dec.map′ Rel≡⇒≡ ≡⇒Rel≡ (decidable Fin._≟_ nf₁ nf₂)
  where open Pointwise

-- We can also give a sound, but not necessarily complete, procedure
-- for determining if two expressions have the same semantics.

prove′ : ∀ {n} (e₁ e₂ : Expr n) → Maybe (∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ)
prove′ e₁ e₂ =
  Maybe.map lemma $ decToMaybe (normalise e₁ ≟ normalise e₂)
  where
  lemma : normalise e₁ ≡ normalise e₂ → ∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ
  lemma eq ρ =
    R.prove ρ e₁ e₂ (begin
      ⟦ normalise e₁ ⟧⇓ ρ  ≡⟨ P.cong (λ e → ⟦ e ⟧⇓ ρ) eq ⟩
      ⟦ normalise e₂ ⟧⇓ ρ  ∎)

-- This procedure can be combined with from-just.

prove : ∀ n (es : Expr n × Expr n) →
        From-just (∀ ρ → ⟦ proj₁ es ⟧ ρ ≈ ⟦ proj₂ es ⟧ ρ)
                  (uncurry prove′ es)
prove _ = from-just ∘ uncurry prove′
