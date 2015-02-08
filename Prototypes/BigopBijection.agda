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

  enum : ∀ {n : ℕ} {a} {A : Set a} → FinType {n} A → Vec A n
  enum enumA = tabulate (_⟨$⟩_ to)
    where
      open import Function.Equality using (_⟨$⟩_)
      open Bijection enumA
{-
  ¬sucm≤n→n≥m : ∀ {m n} → ¬ suc m N≤ n → n N≥ m
  ¬sucm≤n→n≥m x = {!!}

  SumFinType : ∀ {a b} {m n : ℕ} {A : Set a} {B : Set b} → FinType {m} A → FinType {n} B → FinType {m N+ n} (A ⊎ B)
  SumFinType {m = m} {n = n} {A = A} {B = B} enumA enumB = bijection
    where
      bijection = record { to = Fin⟶A⊎B ; bijective = bijective }
        where
          open import Function.Equality using (_⟨$⟩_)
          open import Relation.Nullary using (yes ; no)
          open import Relation.Nullary.Decidable using (toWitness)

          toA = Bijection.to enumA
          toB = Bijection.to enumB

          toA⊎B : Fin (m N+ n) → A ⊎ B
          toA⊎B i with suc (toℕ i) N≤? m | suc (toℕ i ∸ m) N≤? n
          ... | yes suci≤m | _ =         inj₁ (toA ⟨$⟩ fromℕ≤ {toℕ i} suci≤m)
          ... | no  suci≰m | yes i-m≤n = inj₂ (toB ⟨$⟩ fromℕ≤ {toℕ i ∸ m} i-m≤n)
          ... | no  suci≰m | no  i-m≰n = {!!}
            where
              m≥i = ¬sucm≤n→n≥m {!!}

          fromA⊎B : A ⊎ B → Fin (m N+ n)
          fromA⊎B = {!!}

          Fin⟶A⊎B = P.→-to-⟶ toA⊎B
          A⊎B⟶Fin = P.→-to-⟶ fromA⊎B

          bijective = record { injective = injective {!!} ; surjective = surjective }
            where
              injective = {!!}
              surjective = record { from = A⊎B⟶Fin ; right-inverse-of = right-inv }
                where
                  open import Function.LeftInverse
                  right-inv : A⊎B⟶Fin RightInverseOf Fin⟶A⊎B
                  right-inv x = {!!}
-}
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
    { size = size ; Index = Fin size ; Result = ℕ
    ; index = FinFinType ; ε = zero ; _·_ = _N+_ ; comm = comm
    }
    where
      size = suc n

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

  foldr′ : ∀ {a} {A : Set a} {m} → Op₂ A → A → Vec A m → A
  foldr′ {a} {A} op = foldr {a} {a} {A} (λ _ → A) op

  module BigopLemmas {i r} (bigop : Bigop {i} {r}) where
    open Bigop bigop
    import Algebra.FunctionProperties as FP
    open FP {A = Result} _≡_ hiding (Op₂)
    open import Data.Nat
    open import Data.Nat.Properties.Simple
    open import Data.Product
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

    initLast-∷ʳ : ∀ {m} {a} {A : Set a} (xs : Vec A m) (x : A) →
                     initLast (xs ∷ʳ x) ≡ (xs , x , refl)
    initLast-∷ʳ {zero}  []        _  = refl
    initLast-∷ʳ {suc m} (x₁ ∷ xs) x¹ rewrite initLast-∷ʳ {m} xs x¹ = refl

    foldr′-lemmaˡ : ∀ {m : ℕ} {v : Vec Result (suc m)} →
                    foldr′ _·_ ε v ≡ head v · foldr′ _·_ ε (tail v)
    foldr′-lemmaˡ {zero}  {x ∷ []} rewrite idʳ x                 = refl
    foldr′-lemmaˡ {suc m} {x ∷ v}  rewrite foldr′-lemmaˡ {m} {v} = refl

    foldr′-lemmaʳ : ∀ {m : ℕ} {v : Vec Result (suc m)} →
                    foldr′ _·_ ε v ≡ foldr′ _·_ ε (init v) · last v
    foldr′-lemmaʳ {zero}  {x ∷ []} rewrite idˡ x | idʳ x = refl
    foldr′-lemmaʳ {suc m} {x₁ ∷ v} with initLast v
    foldr′-lemmaʳ {suc m} {x₁ ∷ .(v′ ∷ʳ x¹)} | v′ , x¹ , refl
      rewrite
        assoc x₁ (foldr′ _·_ ε v′) x¹
      | foldr′-lemmaʳ {m} {v′ ∷ʳ x¹}
      | initLast-∷ʳ v′ x¹ = refl

  _⟦_⟧ : ∀ {i r} → (o : Bigop {i} {r}) → (Bigop.Index o → Bigop.Result o) → (Bigop.Result o)
  _⟦_⟧ {i} {r} o f = fold· (map f (enum index))
    where
      open Bigop o

      fold· : Vec Result size → Result
      fold· results = foldr′ _·_ ε results

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
