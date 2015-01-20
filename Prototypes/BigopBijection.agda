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

  Enum : ∀ {n : Nat.ℕ} {a ℓ} → (A : Setoid a ℓ) → Set _
  Enum {n = n} A = Bijection (P.setoid (Fin n)) A

  record Bigop {i r ℓ} : Set (L.suc (i L.⊔ r L.⊔ ℓ)) where
    field
      size         : Nat.ℕ
      Index        : Setoid i ℓ
      Result       : Set r
      ε            : Result
      enum         : Enum {size} Index

  BoolEnum : Enum (P.setoid Bool.Bool)
  BoolEnum = record { to = Fin⟶Bool ; bijective = bijective }
    where
      enumTo : Fin 2 → Bool.Bool
      enumTo zero    = Bool.true
      enumTo (suc x) = Bool.false

      enumFrom : Bool.Bool → Fin 2
      enumFrom Bool.true  = zero
      enumFrom Bool.false = suc zero
      
      Fin⟶Bool = record { _⟨$⟩_ = enumTo ; cong = λ x → {!!} }

      bijective = record { injective = λ {x} {y} → injective x y ; surjective = record { from = record { _⟨$⟩_ = {!enumFrom!} ; cong = {!!} } ; right-inverse-of = {!!} } }
        where
          surjective : (x : Fin 2) → (y : Fin 2) → x ≡ y → (enumTo x) ≡ (enumTo y)
          surjective zero           zero           x≡y = P.refl
          surjective zero           (suc y)        ()
          surjective (suc x)        zero           ()
          surjective (suc zero)     (suc zero)     x≡y = P.refl
          surjective (suc zero)     (suc (suc ())) ()
          surjective (suc (suc ())) (suc y)

          injective : (x : Fin 2) → (y : Fin 2) → (enumTo x) ≡ (enumTo y) → x ≡ y
          injective zero           zero           enumx≡enumy = P.refl
          injective zero           (suc y)        ()
          injective (suc x)        zero           ()
          injective (suc zero)     (suc zero)     enumx≡enumy = P.refl
          injective (suc zero)     (suc (suc ()))
          injective (suc (suc ())) (suc y)        enumx≡enumy

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
          
