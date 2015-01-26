module Prototypes.BigopBijection where

--  open import Primitive hiding (suc)

  open import Function.Bijection
  import Data.Nat as Nat
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

  Enum : ∀ {n : Nat.ℕ} {a} → (A : Set a) → Set _
  Enum {n = n} A = Bijection (P.setoid (Fin n)) (P.setoid A)

  record Bigop {i r} : Set (L.suc (i L.⊔ r)) where
    field
      size         : Nat.ℕ
      Index        : Set i
      Result       : Set r
      ε            : Result
      enum         : Enum {size} Index

  enum : ∀ {n : Nat.ℕ} {a} {A : Set a} → Enum {n} A → Vec A n
  enum enumA = tabulate (_⟨$⟩_ (Bijection.to enumA))
    where
      open import Function.Equality using (_⟨$⟩_)

  ¬sucm≤n→n≥m : ∀ {m n} → ¬ Nat.suc m Nat.≤ n → n Nat.≥ m
  ¬sucm≤n→n≥m x = {!!}

  SumEnum : ∀ {a b} {m n : Nat.ℕ} {A : Set a} {B : Set b} → Enum {m} A → Enum {n} B → Enum {m Nat.+ n} (A ⊎ B)
  SumEnum {m = m} {n = n} {A = A} {B = B} enumA enumB = bijection
    where
      bijection = record { to = P.→-to-⟶ toA⊎B ; bijective = bijective }
        where
          open import Function.Equality using (_⟨$⟩_)
          open import Relation.Nullary using (yes ; no)
          open import Relation.Nullary.Decidable using (toWitness)

          toA = Bijection.to enumA
          toB = Bijection.to enumB

          toA⊎B : Fin (m Nat.+ n) → A ⊎ B
          toA⊎B i with Nat.suc (toℕ i) Nat.≤? m | Nat.suc (toℕ i Nat.∸ m) Nat.≤? n
          ... | yes suci≤m | _ =         inj₁ (toA ⟨$⟩ fromℕ≤ {toℕ i} suci≤m)
          ... | no  suci≰m | yes i-m≤n = inj₂ (toB ⟨$⟩ fromℕ≤ {toℕ i Nat.∸ m} i-m≤n)
          ... | no  suci≰m | no  i-m≰n = {!!}
            where
              m≥i = ¬sucm≤n→n≥m {!!}

          bijective = {!!}

  BoolEnum : Enum Bool.Bool
  BoolEnum = record { to = Fin⟶Bool ; bijective = bijective }
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


  FinEnum : ∀ {n : Nat.ℕ} → Enum {n} (Fin n)
  FinEnum = record { to = Fin⟶Nat ; bijective = bijective }
    where
      Fin⟶Nat = record { _⟨$⟩_ = Fun.id ; cong = Fun.id }
      bijective = record { injective = Fun.id ; surjective = surjective }
        where
          surjective = record { from = Fin⟶Nat ; right-inverse-of = right-inv }
            where
              right-inv = λ x → P.refl

  finSumBigop : (n : Nat.ℕ) → Bigop
  finSumBigop n = record { size = size ; Index = Fin size ;
                           Result = Nat.ℕ ; enum = FinEnum ; ε = Nat.zero}
    where
      size = Nat.suc n

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
      injective {suc zero}     {suc zero} fx≡fy = P.refl
      injective {suc (suc ())}            fx≡fy
