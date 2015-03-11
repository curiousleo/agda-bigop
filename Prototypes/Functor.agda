module Prototypes.Functor where

--  open import Category.Functor
  open import Data.Product

  open import Function

  open import Level

  import Relation.Binary as B
  import Relation.Binary.Indexed as I

  IFun : ∀ {i} → Set i → (ℓ : Level) → Set _
  IFun I ℓ = I → I → Set ℓ → Set ℓ

  record IsApplicative {f ℓ} (F : Set f → Set f) (_≈_ : I.Rel F ℓ)
                       (pure : ∀ {A} → A → F A)
                       (_⊛_  : ∀ {A B} → F (A → B) → F A → F B) :
                       Set (suc f ⊔ ℓ) where    
    field
      isEquivalence : I.IsEquivalence F _≈_
      identity      : ∀ {A B : Set f} (u : F (A → B)) →
                      (pure id ⊛ u) ≈ u
      composition   : ∀ {A B C D : Set f} (u : F (A → B → C)) v (w : F D) →
                      (pure (_∘′_ {A = A} {B} {C}) ⊛ (u ⊛ (v ⊛ w))) ≈ (u ⊛ (v ⊛ w))
      homomorphism  : ∀ {A B} (g : A → B) x →
                      (pure g ⊛ pure x) ≈ (pure (g x))
      interchange   : ∀ {A B} (u : F (A → B)) x →
                      (u ⊛ pure x) ≈ (pure (λ g → g x) ⊛ u)

  record Applicative {f ℓ} (F : Set f → Set f) :
                      Set (suc f ⊔ suc ℓ) where
    infixl 4 _⊛_
    field
      pure : ∀ {A} → A → F A
      _⊛_  : ∀ {A B} → F (A → B) → F A → F B
      _≈_  : I.Rel F ℓ
      isApplicative : IsApplicative F _≈_ pure _⊛_

{-
  record IsCommutingTriangle {a b c}
                             {A : Set a} {B : Set b} {C : Set c}
                             (f : A → B) (g : B → C) (h : A → C) : Set _ where
    field
      Commutes : g ∘ f ≗ h
-}
{-
  Commutes : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
             Triangle A B C → Set _
  Commutes (f , g , h) = g ∘ f ≗ h
    where
      open import Relation.Binary.PropositionalEquality

  RespectsCommutingTriangles : ∀ {i f} {I : Set i}
                               {a b c} {A : Set a} {B : Set b} {C : Set c} →
                               IFun I f → Set _
  RespectsCommutingTriangles {A = A} {B} {C} F =
    ∀ (f : A → B) (g : B → C) (h : A → C) → g ∘ f ≗ h → F (g ∘ f) ≗ F h
    where
      open import Relation.Binary.PropositionalEquality
-}
{-
  record IsIApplicative {i f ℓ} {I : Set i} (F : IFun I f) (_≈_  : I.Rel I ℓ)
                        (pure : ∀ {i A} → A → F i i A)
                        (_⊛_ : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B)
                        : Set (suc ℓ) where
    field
      isEquivalence        : IsEquivalence _≈_
      preservesComposition : Preser
-}

{-
  record IApplicative {i f ℓ} {I : Set i} (F : IFun I f) :
                      Set (i ⊔ suc f ⊔ suc ℓ) where
    infixl 4 _⊛_
    -- infix  4 _⊗_

    field
      pure : ∀ {i A} → A → F i i A
      _⊛_  : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B
      _≈_  : I.Rel pure ℓ
--      isIApplicative : IsIApplicative F _≈_ pure _⊛_
-}

{-
  record IsFunctor {ℓ} {F : Set ℓ → Set ℓ} (_≈_ : ∀ {B} → Rel (F B) ℓ)
                   (<$> : ∀ {A B} → (A → B) → F A → F B) : Set (suc ℓ) where
    field
      isEquivalence        : ∀ {B} → IsEquivalence (_≈_ {B})
      preservesComposition : ∀ {A} (x : A) → ∀ f g → (g ∘ f) <$> x ≈ g <$> (f <$> x)
      preservesIdentity    : ∀ {A} (x : A) → id <$> x ≈ x

  record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
    infixl 4 _<$>_
    field
      _<$>_     : ∀ {A B} → (A → B) → F A → F B
      _≈_       : ∀ {B} → Rel (F B) ℓ
      isFunctor : IsFunctor _≈_ _<$>_

    open IsFunctor isFunctor public
-}
