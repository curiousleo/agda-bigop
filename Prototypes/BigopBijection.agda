module Prototypes.BigopBijection where

--  open import Primitive hiding (suc)

  open import Function.Bijection renaming (_∘_ to _∘B_)
  open import Function.Surjection hiding (_∘_)
  open import Data.Nat renaming (_+_ to _N+_ ; _≤_ to _N≤_ ; _≥_ to _N≥_ ; _≤?_ to _N≤?_)
  import Level as L
  open import Data.Fin
  import Relation.Binary.PropositionalEquality as P
  open import Relation.Binary
  open import Relation.Binary.Core using (_≡_)
  import Function as Fun
  import Data.Bool as Bool
  open import Data.Vec
  open import Data.Sum hiding (map)
  open import Relation.Nullary using (¬_)
  open import Function.Equality using (_⟨$⟩_)
  open import Algebra.FunctionProperties using (Op₂)
  open import Algebra.Structures

  FinType : ∀ {n : ℕ} {a} → (A : Set a) → Set _
  FinType {n = n} A = Bijection (P.setoid (Fin n)) (P.setoid A)

  record Bigop {i r} : Set (L.suc (i L.⊔ r)) where
    field
      size         : ℕ
      Index        : Set i
      Result       : Set r
      ε            : Result
      index        : FinType {size} Index
      _·_          : Op₂ Result
      comm         : IsCommutativeMonoid _≡_ _·_ ε

  enum : ∀ {n} {a} {A : Set a} → FinType {n} A → Vec A n
  enum enumA = tabulate (_⟨$⟩_ to)
    where
      open import Function.Equality using (_⟨$⟩_)
      open Bijection enumA

  BoolFinType : FinType Bool.Bool
  BoolFinType = record { to = Fin⟶Bool ; bijective = bijective }
    where
      enumTo : Fin 2 → Bool.Bool
      enumTo zero    = Bool.true
      enumTo (suc x) = Bool.false

      enumFrom : Bool.Bool → Fin 2
      enumFrom Bool.true  = zero
      enumFrom Bool.false = suc zero

      Fin⟶Bool = P.→-to-⟶ enumTo
      Bool⟶Fin = P.→-to-⟶ enumFrom

      bijective = record { injective = injective ; surjective = surjective }
        where
          injective : {x y : Fin 2} → (enumTo x) ≡ (enumTo y) → x ≡ y
          injective {zero}         {zero}         enumx≡enumy = P.refl
          injective {zero}         {suc y}        ()
          injective {suc x}        {zero}         ()
          injective {suc zero}     {suc zero}     enumx≡enumy = P.refl
          injective {suc zero}     {suc (suc ())} enumx≡enumy
          injective {suc (suc ())} {suc y}        enumx≡enumy

          surjective = record { from = Bool⟶Fin ; right-inverse-of = right-inv }
            where
              open import Function.LeftInverse
              right-inv : Bool⟶Fin RightInverseOf Fin⟶Bool
              right-inv Bool.true  = P.refl
              right-inv Bool.false = P.refl


  FinFinType : ∀ {n : ℕ} → FinType {n} (Fin n)
  FinFinType = record { to = Fin⟶Nat ; bijective = bijective }
    where
      Fin⟶Nat = record { _⟨$⟩_ = Fun.id ; cong = Fun.id }
      bijective = record { injective = Fun.id ; surjective = surjective }
        where
          surjective = record { from = Fin⟶Nat ; right-inverse-of = right-inv }
            where
              right-inv = λ x → P.refl

  finSumBigop : (n : ℕ) → Bigop
  finSumBigop n = record
    { size = n ; Index = Fin n ; Result = ℕ
    ; index = FinFinType ; ε = zero ; _·_ = _N+_ ; comm = comm
    }
    where
      open import Data.Nat.Properties.Simple
      comm : IsCommutativeMonoid _≡_ _N+_ zero
      comm = record
        { isSemigroup = record
          { isEquivalence = P.isEquivalence
          ; assoc = +-assoc
          ; ∙-cong = P.cong₂ _N+_
          }
        ; identityˡ = λ x → P.refl
        ; comm = +-comm
        }

  module BigopLemmas {i r} (bigop : Bigop {i} {r}) where
    open Bigop bigop
    import Algebra.FunctionProperties as FP
    open FP {A = Result} _≡_ hiding (Op₂)
    open import Data.Nat
    open import Data.Nat.Properties.Simple
    open import Data.Product hiding (map)
    open import Relation.Binary.PropositionalEquality
    open import Algebra
    import Relation.Binary.Vec.Pointwise as PW

    assoc : Associative _·_
    assoc = IsSemigroup.assoc (IsCommutativeMonoid.isSemigroup comm)

    identity : Identity ε _·_
    identity = IsMonoid.identity (IsCommutativeMonoid.isMonoid comm)

    idˡ : LeftIdentity ε _·_
    idˡ = proj₁ identity

    idʳ : RightIdentity ε _·_
    idʳ = proj₂ identity

    fold· : ∀ {m : ℕ} → Vec Result m → Result
    fold· = foldr (λ _ → Result) _·_ ε

    initLast-∷ʳ : ∀ {m} {a} {A : Set a} (xs : Vec A m) (x : A) →
                  initLast (xs ∷ʳ x) ≡ (xs , x , refl)
    initLast-∷ʳ {zero}  []        _  = refl
    initLast-∷ʳ {suc m} (x₁ ∷ xs) x¹ rewrite initLast-∷ʳ {m} xs x¹ = refl

    fold·-lemmaˡ : ∀ {m : ℕ} (v : Vec Result (suc m)) →
                   fold· v ≡ head v · fold· (tail v)
    fold·-lemmaˡ {zero}  (x ∷ []) rewrite idʳ x              = refl
    fold·-lemmaˡ {suc m} (x ∷ v)  rewrite fold·-lemmaˡ {m} v = refl

    fold·-lemmaʳ : ∀ {m : ℕ} (v : Vec Result (suc m)) →
                   fold· v ≡ fold· (init v) · last v
    fold·-lemmaʳ {zero}  (x ∷ []) rewrite idˡ x | idʳ x = refl
    fold·-lemmaʳ {suc m} (x ∷ v) with initLast v
    fold·-lemmaʳ {suc m} (x ∷ .(v′ ∷ʳ x′)) | v′ , x′ , refl
      rewrite
        assoc x (fold· v′) x′
      | fold·-lemmaʳ {m} (v′ ∷ʳ x′)
      | initLast-∷ʳ v′ x′ = refl

    head-map : ∀ {m} {v : Vec Index (suc m)} (f : Index → Result) →
               head (f ∷ replicate f ⊛ v) ≡ f (head v)
    head-map {zero}  {_ ∷ []} f = refl
    head-map {suc m} {x ∷ v}  f = refl

    last-lemma : ∀ {a} {A : Set a} {m} (y : A) (ys : Vec A (suc m)) →
                 last (y ∷ ys) ≡ last ys
    last-lemma y ys with initLast ys
    last-lemma y .(v′ ∷ʳ x′) | v′ , x′ , refl = refl

    last-map : ∀ {m} {v : Vec Index (suc m)} (f : Index → Result) →
               last (f ∷ replicate f ⊛ v) ≡ f (last v)
    last-map {zero}  {_ ∷ []} f = refl
    last-map {suc m} {x ∷ v}  f with initLast v
    last-map {suc m} {x ∷ .(v′ ∷ʳ x′)} f | v′ , x′ , refl
      rewrite
        last-lemma {m = m} (f x) (f ∷ replicate f ⊛ v′ ∷ʳ x′)
      | last-map {m} {v′ ∷ʳ x′} f
      | initLast-∷ʳ v′ x′ = refl

    fold·-map-lemmaˡ : ∀ {m} (v : Vec Index (suc m)) (f : Index → Result) →
                       fold· (map f v) ≡ f (head v) · fold· (tail (map f v))
    fold·-map-lemmaˡ {m} v f
      rewrite
        fold·-lemmaˡ (map f v)
      | head-map {v = v} f = refl

    fold·-map-lemmaʳ : ∀ {m} (v : Vec Index (suc m)) (f : Index → Result) →
                       fold· (map f v) ≡ fold· (init (map f v)) · f (last v)
    fold·-map-lemmaʳ {m} v f
      rewrite
        fold·-lemmaʳ (map f v)
      | last-map {v = v} f = refl

  _⟦_⟧ : ∀ {i r} → (o : Bigop {i} {r}) → (Bigop.Index o → Bigop.Result o) → (Bigop.Result o)
  _⟦_⟧ {i} {r} o f = fold· (map f (enum index))
    where
      open Bigop o
      open BigopLemmas o

{-
  dist-enums-⊎ : ∀ {a b} {m n : ℕ} {A : Set a} {B : Set b} →
                 FinType {m} A → FinType {n} B → FinType {m N+ n} (A ⊎ B)
  dist-enums-⊎ {m = m} {n = n} {A = A} {B = B} enumA enumB = enumA⊎B
    where
      open Bijection enumA renaming (to to toA ; bijective to bijectiveA)
      open Bijection enumB renaming (to to toB ; bijective to bijectiveB)

      open Surjective (Bijective.surjective bijectiveA) renaming (from to fromA)
      open Surjective (Bijective.surjective bijectiveB) renaming (from to fromB)

      open import Data.Sum
      open import Prototypes.FinSum

      toA⊎B : Fin (m N+ n) → A ⊎ B
      toA⊎B = [ ? , ? ]′ ∘ m+n→m⊎n

      fromA⊎B : A ⊎ B → Fin (m N+ n)
      fromA⊎B = [ (inject+ n Fun.∘ _⟨$⟩_ fromA) , (raise m Fun.∘ _⟨$⟩_ fromB) ]′

      Fin⟶A⊎B = P.→-to-⟶ toA⊎B
      A⊎B⟶Fin = P.→-to-⟶ fromA⊎B

      injectiveA⊎B : Injective Fin⟶A⊎B
      injectiveA⊎B = {!!}

      surjectiveA⊎B : Surjective Fin⟶A⊎B
      surjectiveA⊎B = record { from = A⊎B⟶Fin ; right-inverse-of = {!!} }

      bijectiveA⊎B : Bijective Fin⟶A⊎B
      bijectiveA⊎B = record { injective = injectiveA⊎B ; surjective = surjectiveA⊎B }

      enumA⊎B : FinType {m N+ n} (A ⊎ B)
      enumA⊎B = record { to = Fin⟶A⊎B ; bijective = bijectiveA⊎B }
-}
