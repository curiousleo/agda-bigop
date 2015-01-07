module Prototypes.BigopInjection where

  import Function as Fun
  open import Function.Injection hiding (id)
  open import Function.Equality
  open import Algebra.FunctionProperties.Core
  open import Algebra.Structures
  import Relation.Binary.PropositionalEquality as P
  open import Data.Fin
  import Data.Nat as Nat
  import Data.List as List
  import Data.Bool as Bool
  import Relation.Binary as B
  import Relation.Binary.Indexed as I
  open import Level
    renaming (zero to zeroℓ ; suc to sucℓ ; _⊔_ to _⊔ℓ_)

  Enum : ∀ {n : Nat.ℕ} {a} → (A : Set a) → Set _
  Enum {n = n} A = Fin n ↣ A

  record Bigop {r i} : Set (sucℓ (r ⊔ℓ i)) where
    field
      size        : Nat.ℕ
      Index       : Set i
      Result      : Set r
      ε           : Result
      enum        : Enum {size} Index

  record BigopExpr {bigop : Bigop} : Set _ where
    open Bigop bigop
    field
      Expr        : Index → Result
      _·_         : Result → Result → Result
      isMonoid    : IsMonoid P._≡_ _·_ ε
      

  finSumBigop : (n : Nat.ℕ) → Bigop
  finSumBigop n = record {size = (Nat.suc n) ; Index = Fin (Nat.suc n) ; Result = Nat.ℕ ; enum = enum ; ε = Nat.zero}
    where
      enum = record { to = id ; injective = Fun.id }

  orBigop : Bigop
  orBigop = record {size = 2 ; Index = Bool.Bool ; Result = Bool.Bool ; enum = enum ; ε = Bool.false}
    where
      open I using (_=[_]⇒_)
      injection : Fin 2 → Bool.Bool
      injection zero = Bool.true
      injection (suc n) = Bool.false
      cong′ : B.Setoid._≈_ (P.setoid (Fin 2)) =[ injection ]⇒ I.Setoid._≈_ (B.Setoid.indexedSetoid (P.setoid Bool.Bool))
      cong′ P.refl = P.refl
      Fin2⟶Bool : P.setoid (Fin 2) ⟶ P.setoid Bool.Bool
      Fin2⟶Bool = record { _⟨$⟩_ = injection ; cong = cong′ }
      injective : Injective Fin2⟶Bool
      injective = inj
        where
          open B.Setoid (P.setoid (Fin 2)) renaming (_≈_ to _≈₁_)
          open B.Setoid (P.setoid Bool.Bool) renaming (_≈_ to _≈₂_)
          inj : Injective Fin2⟶Bool
          inj {zero} {zero} f = P.refl
          inj {zero} {suc y₁} f = {!!}
          inj {suc x₁} {zero} f = {!!}
          inj {suc x₁} {suc y₁} f = {!!}
      enum = record {to = Fin2⟶Bool ; injective = injective }

  finSum : (n : Nat.ℕ) → BigopExpr {finSumBigop n}
  finSum n = record { Expr = toℕ ; _·_ = Nat._+_ ; isMonoid = isMonoid }
    where
      open Bigop (finSumBigop n)
      isMonoid = {!!}

  foldBigop : (bigop : Bigop) → (expr : BigopExpr {bigop}) → (Bigop.Result bigop)
  foldBigop bigop expr = List.foldr _·_ ε {!map !}
    where
      open Bigop bigop
      open BigopExpr expr
