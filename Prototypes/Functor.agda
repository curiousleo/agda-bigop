module Prototypes.Functor where

--  open import Category.Functor
  open import Data.Product

  open import Function

  open import Level

  import Relation.Binary as B
  import Relation.Binary.Indexed as I

  record IsFunctor {f ℓ} (F : Set f → Set f) (_≈_ : I.Rel F ℓ)
                   (_<$>_ : ∀ {A B} → (A → B) → F A → F B) :
                   Set (suc f ⊔ ℓ) where
    field
      isEquivalence : I.IsEquivalence F _≈_
      identity      : ∀ {A} (x : F A) → (id <$> x) ≈ x
      composition   : ∀ {A B C} (f : B → C) g (x : F A) →
                      ((f ∘′ g) <$> x) ≈ (f <$> (g <$> x))

  record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
    infixl 4 _<$>_
    field
      _<$>_     : ∀ {A B} → (A → B) → F A → F B
      _≈_       : I.Rel F ℓ
      isFunctor : IsFunctor F _≈_ _<$>_

  record IsMonad {f ℓ} (F : Set f → Set f) (_≈_ : I.Rel F ℓ)
                 (return : ∀ {A} → A → F A)
                 (_>>=_  : ∀ {A B} → F A → (A → F B) → F B) :
                 Set (suc f ⊔ ℓ) where
    field
      isEquivalence : I.IsEquivalence F _≈_
      identityˡ     : ∀ {A B} (v : A) (k : A → F B) →
                      (return v >>= k) ≈ k v
      identityʳ     : ∀ {A} (v : F A) →
                      (v >>= return) ≈ v
      assoc         : ∀ {A B C} (m : F A) (f : A → F B) (g : B → F C) →
                      ((m >>= f) >>= g) ≈ (m >>= (λ x → f x >>= g))

  record Monad {f ℓ} (F : Set f → Set f) :
               Set (suc f ⊔ suc ℓ) where
    infixl 1 _>>=_
    field
      return  : ∀ {A} → A → F A
      _>>=_   : ∀ {A B} → F A → (A → F B) → F B
      _≈_     : I.Rel F ℓ
      isMonad : IsMonad F _≈_ return _>>=_

    open IsMonad isMonad public

  record IsApplicative {f ℓ} (F : Set f → Set f) (_≈_ : I.Rel F ℓ)
                       (pure : ∀ {A} → A → F A)
                       (_⊛_  : ∀ {A B} → F (A → B) → F A → F B) :
                       Set (suc f ⊔ ℓ) where    
    field
      isEquivalence : I.IsEquivalence F _≈_
--    identity      : ∀ {A B : Set f} (u : F (A → B)) →
--                    (pure id ⊛ u) ≈ u
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
      pure          : ∀ {A} → A → F A
      _⊛_           : ∀ {A B} → F (A → B) → F A → F B
      _≈_           : I.Rel F ℓ
      isFunctor     : IsFunctor F _≈_ (λ f x → pure f ⊛ x)
      isApplicative : IsApplicative F _≈_ pure _⊛_

    _<$>_ : ∀ {A B} → (A → B) → F A → F B
    f <$> x = (pure f) ⊛ x

  IFun : ∀ {i} → Set i → (ℓ : Level) → Set _
  IFun I ℓ = I → I → Set ℓ → Set ℓ

  module _ where
    Monad→Applicative : ∀ {f ℓ} {F : Set f → Set f} →
                        Monad {f} {ℓ} F → Applicative {f} {ℓ} F
    Monad→Applicative {f} {ℓ} {F} m = record
      { pure          = return
      ; _⊛_           = _⊛_
      ; _≈_           = _≈_
      ; isFunctor     = isFunctor
      ; isApplicative = isApplicative
      }
      where
        open Monad m

        _⊛_ : ∀ {A B} → F (A → B) → F A → F B
        f ⊛ v = f >>= (λ g →
                v >>= return ∘′ g)

        _<$>_ : ∀ {A B} → (A → B) → F A → F B
        f <$> x = (return f) ⊛ x

        isFunctor : IsFunctor F _≈_ _<$>_
        isFunctor = record
          { isEquivalence = isEquivalence
          ; identity      = identity
          ; composition   = composition
          }
          where
            open I.IsEquivalence isEquivalence

            identity : {A : Set f} (x : F A) → (id <$> x) ≈ x
            identity _ = trans (identityˡ _ _) (identityʳ _)

            composition : ∀ {A B C} (f : B → C) g (x : F A) →
                          ((f ∘′ g) <$> x) ≈ (f <$> (g <$> x))
            composition f g x = trans (identityˡ _ _) (sym (trans (identityˡ _ _) (trans (assoc _ _ _) (trans (identityˡ _ _) {!!}))))

        isApplicative : IsApplicative F _≈_ return _⊛_
        isApplicative = record
          { isEquivalence = isEquivalence
--        ; identity      = identity
          ; composition   = composition
          ; homomorphism  = homomorphism
          ; interchange   = interchange
          }
          where
            open I.IsEquivalence isEquivalence

            composition : ∀ {A B C D : Set f} (u : F (A → B → C)) v (w : F D) →
                          (return (_∘′_ {A = A} {B} {C}) ⊛ (u ⊛ (v ⊛ w))) ≈
                          (u ⊛ (v ⊛ w))
            composition u v w = trans (identityˡ _ _) {!!}

            homomorphism : ∀ {A B : Set f} (f : A → B) (v : A) →
                           ((return f) ⊛ (return v)) ≈ (return (f v))
            homomorphism f v = trans (identityˡ _ _) (identityˡ _ _)

            interchange : ∀ {A B} (u : F (A → B)) x →
                          (u ⊛ return x) ≈ (return (λ g → g x) ⊛ u)
            interchange u x = sym (trans (identityˡ _ _) {!!})

{-
  record IsIApplicative {i f ℓ} {I : Set i} (F : IFun I f) (_≈_ : I.Rel {!!} ℓ)
                       (pure : ∀ {i A} → A → F i i A)
                       (_⊛_ : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B) :
                       Set (i ⊔ suc f ⊔ ℓ) where
    field
      isEquivalence : I.IsEquivalence {!!} _≈_
      identity      : ∀ {i j A B} (u : F i j (A → B)) →
                      (pure (id {A = {!!}}) ⊛ u) ≈ u
      composition   : ∀ {i j k l A B C D} (u : F i j (A → B → C)) (v : F j k (D → A)) (w : F k l D) →
                      (pure (_∘′_ {A = A} {B} {C}) ⊛ (u ⊛ (v ⊛ w))) ≈ (u ⊛ (v ⊛ w))
      homomorphism  : ∀ {i A B} (g : A → B) x →
                      (pure g ⊛ pure x) ≈ (pure (g x))
      interchange   : ∀ {i j A B} (u : F i j (A → B)) x →
                      (u ⊛ pure x) ≈ (pure (λ g → g x) ⊛ u)

  record IApplicative {i f ℓ} {I : Set i} (F : IFun I f) :
                      Set (i ⊔ suc f ⊔ suc ℓ) where
    infixl 4 _⊛_
    -- infix  4 _⊗_

    field
      pure : ∀ {i A} → A → F i i A
      _⊛_  : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B
      _≈_  : I.Rel {!!} ℓ
      isIApplicative : IsIApplicative F _≈_ pure _⊛_
-}
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
