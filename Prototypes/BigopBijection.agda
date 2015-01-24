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

  Enum : ∀ {n : Nat.ℕ} {a ℓ} → (A : Setoid a ℓ) → Set _
  Enum {n = n} A = Bijection (P.setoid (Fin n)) A

  record Bigop {i r ℓ} : Set (L.suc (i L.⊔ r L.⊔ ℓ)) where
    field
      size         : Nat.ℕ
      Index        : Setoid i ℓ
      Result       : Set r
      ε            : Result
      enum         : Enum {size} Index

  enum : ∀ {n : Nat.ℕ} {a ℓ} {A : Setoid a ℓ} → Enum {n} A → Vec (Setoid.Carrier A) n
  enum enumA = tabulate (_⟨$⟩_ (Bijection.to enumA))
    where
      open import Function.Equality using (_⟨$⟩_)

  BoolEnum : Enum (P.setoid Bool.Bool)
  BoolEnum = record { to = Fin⟶Bool ; bijective = bijective }
    where
      enumTo : Fin 2 → Bool.Bool
      enumTo zero    = Bool.true
      enumTo (suc x) = Bool.false

      enumFrom : Bool.Bool → Fin 2
      enumFrom Bool.true  = zero
      enumFrom Bool.false = suc zero
      
      Fin⟶Bool = record { _⟨$⟩_ = enumTo ; cong = cong }
        where
          cong : {x y : Fin 2} → x ≡ y → enumTo x ≡ enumTo y
          cong {zero}  P.refl = P.refl
          cong {suc x} P.refl = P.refl

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
              Bool⟶Fin = record { _⟨$⟩_ = enumFrom ; cong = cong }
                where
                  cong : {x y : Bool.Bool} → x ≡ y → enumFrom x ≡ enumFrom y
                  cong {Bool.true}  P.refl = P.refl
                  cong {Bool.false} P.refl = P.refl

              open import Function.LeftInverse
              right-inv : Bool⟶Fin RightInverseOf Fin⟶Bool
              right-inv Bool.true  = P.refl
              right-inv Bool.false = P.refl


  FinEnum : ∀ {n : Nat.ℕ} → Enum {n} (P.setoid (Fin n))
  FinEnum = record { to = Fin⟶Nat ; bijective = bijective }
    where
      Fin⟶Nat = record { _⟨$⟩_ = Fun.id ; cong = Fun.id }
      bijective = record { injective = Fun.id ; surjective = surjective }
        where
          surjective = record { from = Fin⟶Nat ; right-inverse-of = right-inv }
            where
              right-inv = λ x → P.refl

  finSumBigop : (n : Nat.ℕ) → Bigop
  finSumBigop n = record { size = size ; Index = P.setoid (Fin size) ;
                           Result = Nat.ℕ ; enum = FinEnum ; ε = Nat.zero}
    where
      size = Nat.suc n
          
