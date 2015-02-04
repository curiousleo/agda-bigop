module Prototypes.BigopBijection where

--  open import Primitive hiding (suc)

  open import Function.Bijection hiding (_∘_)
  open import Function.Surjection
  open import Data.Nat renaming (_+_ to _N+_ ; _≤_ to _N≤_ ; _≥_ to _N≥_ ; _≤?_ to _N≤?_)
  import Level as L
  open import Data.Fin
  import Relation.Binary.PropositionalEquality as P
  open import Relation.Binary
  open import Relation.Binary.Core using (_≡_)
  import Function as Fun
  import Data.Bool as Bool
  open import Data.Vec
  open import Data.Sum
  open import Relation.Nullary using (¬_)
  open import Function.Equality using (_⟨$⟩_)

  FinType : ∀ {n : ℕ} {a} → (A : Set a) → Set _
  FinType {n = n} A = Bijection (P.setoid (Fin n)) (P.setoid A)

  record Bigop {i r} : Set (L.suc (i L.⊔ r)) where
    field
      size         : ℕ
      Index        : Set i
      Result       : Set r
      ε            : Result
      enum         : FinType {size} Index

  enum : ∀ {n : ℕ} {a} {A : Set a} → FinType {n} A → Vec A n
  enum enumA = tabulate (_⟨$⟩_ to)
    where
      open import Function.Equality using (_⟨$⟩_)
      open Bijection enumA

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
  finSumBigop n = record { size = size ; Index = Fin size ;
                           Result = ℕ ; enum = FinFinType ; ε = zero}
    where
      size = suc n

-- EXPERIMENT

  data Colour : Set where
    red green blue : Colour

  record NotRed : Set where
    constructor _,_
    field
      colour : Colour
      colour-isn't-red : ¬ (colour ≡ red)

  f : Fin 2 → NotRed
  f zero       = green , (λ ())
  f (suc zero) = blue , (λ ())
  f (suc (suc ()))

  g : NotRed → Fin 2
  g (red   , n) = zero
  g (green , n) = zero
  g (blue  , n) = suc zero

  open import Function.Injection
  finj : Injection (P.setoid (Fin 2)) (P.setoid NotRed)
  finj = record { to = Fin⟶NotRed ; injective = injective }
    where
      Fin⟶NotRed = P.→-to-⟶ f
          
      injective : Injective Fin⟶NotRed
      injective {zero}         {zero}         fx≡fy = P.refl
      injective {zero}         {suc zero} ()
      injective { _ }          {suc (suc ())} fx≡fy
      injective {suc zero}     {zero} ()
      injective {suc zero}     {suc zero}     fx≡fy = P.refl
      injective {suc (suc ())}                fx≡fy

  open import Algebra

  fold∙ : ∀ {n c ℓ} → (m : Monoid c ℓ) →
          Vec (Monoid.Carrier m) n →
          Monoid.Carrier m
  fold∙ m = foldr (λ _ → Carrier) _∙_ ε
    where
      open Monoid m

  dist-enums-⊎ : ∀ {a b} {m n : ℕ} {A : Set a} {B : Set b} →
                 FinType {m} A → FinType {n} B → FinType {m N+ n} (A ⊎ B)
  dist-enums-⊎ {m = m} {n = n} {A = A} {B = B} enumA enumB = enumA⊎B
    where
      open Bijection enumA renaming (to to toA ; bijective to bijectiveA)
      open Bijection enumB renaming (to to toB ; bijective to bijectiveB)

      open Surjective (Bijective.surjective bijectiveA) renaming (from to fromA)
      open Surjective (Bijective.surjective bijectiveB) renaming (from to fromB)

      open import Data.Sum

      toA⊎B : Fin (m N+ n) → A ⊎ B
      toA⊎B x = {!!}

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
