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

  Enum : ∀ {n : ℕ} {a} → (A : Set a) → Set _
  Enum {n = n} A = Bijection (P.setoid (Fin n)) (P.setoid A)

  record Bigop {i r} : Set (L.suc (i L.⊔ r)) where
    field
      size         : ℕ
      Index        : Set i
      Result       : Set r
      ε            : Result
      enum         : Enum {size} Index

  enum : ∀ {n : ℕ} {a} {A : Set a} → Enum {n} A → Vec A n
  enum enumA = tabulate (_⟨$⟩_ to)
    where
      open import Function.Equality using (_⟨$⟩_)
      open Bijection enumA

  ¬sucm≤n→n≥m : ∀ {m n} → ¬ suc m N≤ n → n N≥ m
  ¬sucm≤n→n≥m x = {!!}

  SumEnum : ∀ {a b} {m n : ℕ} {A : Set a} {B : Set b} → Enum {m} A → Enum {n} B → Enum {m N+ n} (A ⊎ B)
  SumEnum {m = m} {n = n} {A = A} {B = B} enumA enumB = bijection
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


  FinEnum : ∀ {n : ℕ} → Enum {n} (Fin n)
  FinEnum = record { to = Fin⟶Nat ; bijective = bijective }
    where
      Fin⟶Nat = record { _⟨$⟩_ = Fun.id ; cong = Fun.id }
      bijective = record { injective = Fun.id ; surjective = surjective }
        where
          surjective = record { from = Fin⟶Nat ; right-inverse-of = right-inv }
            where
              right-inv = λ x → P.refl

  finSumBigop : (n : ℕ) → Bigop
  finSumBigop n = record { size = size ; Index = Fin size ;
                           Result = ℕ ; enum = FinEnum ; ε = zero}
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
                 Enum {m} A → Enum {n} B → Enum {m N+ n} (A ⊎ B)
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

      enumA⊎B : Enum {m N+ n} (A ⊎ B)
      enumA⊎B = record { to = Fin⟶A⊎B ; bijective = bijectiveA⊎B }

  m+n↔m⊎n : ∀ {m n} →
            Bijection (P.setoid (Fin (m N+ n))) (P.setoid (Fin m ⊎ Fin n))
  m+n↔m⊎n = record { to = to⟶ ; bijective = bijective }
    where
      open import Relation.Nullary
      open import Data.Nat.Properties
      open import Function.LeftInverse using (_RightInverseOf_)
      
      to→ : ∀ {m n} → Fin (m N+ n) → Fin m ⊎ Fin n
      to→ {m} {n} i with m N≤? toℕ i
      ... | yes m≤i = inj₂ (reduce≥ i m≤i)
      ... | no ¬m≤i = inj₁ (fromℕ≤ {toℕ i} (≰⇒> ¬m≤i))

      from→ : ∀ {m n} → Fin m ⊎ Fin n → Fin (m N+ n)
      from→ {m} {n} = [ inject+ n , raise m ]′

      to⟶ = P.→-to-⟶ to→
      from⟶ = P.→-to-⟶ from→

      injective : ∀ {m n} → to→ m ≡ to→ n → m ≡ n
      injective {m} {n} tom≡ton = {!!}

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ m → to→ (from→ m) ≡ m -- from⟶ RightInverseOf to⟶
          right-inv m = {!!}

      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }

  suc-injective : ∀ {n} {p q : Fin n} → Data.Fin.suc p ≡ Data.Fin.suc q → p ≡ q
  suc-injective P.refl = P.refl

  inject+k-injective : ∀ {n k} → (i : Fin n) → (j : Fin n) →
                       inject+ k i ≡ inject+ k j → i ≡ j
  inject+k-injective zero zero inj≡ = P.refl
  inject+k-injective zero (suc j) ()
  inject+k-injective (suc i) zero ()
  inject+k-injective (suc i) (suc j) inj≡ = P.cong suc (inject+k-injective i j (suc-injective inj≡))

  raisek-injective : ∀ {n} → (k : ℕ) → (i : Fin n) → (j : Fin n) →
                     raise k i ≡ raise k j → i ≡ j
  raisek-injective zero i .i P.refl = P.refl
  raisek-injective (suc k) i j r≡r = raisek-injective k i j (suc-injective r≡r)

  m+n→n+m : ∀ {m n} → Fin (m N+ n) → Fin (n N+ m)
  m+n→n+m {m} {n} m+n = {!!}

  inject+-raise-injective : (m n : ℕ) → (i : Fin n) → (j : Fin m) →
                            inject+ m i ≡ raise n j → toℕ i ≡ n N+ toℕ j
  inject+-raise-injective m n i j inj≡ =
    begin
      toℕ i
        ≡⟨ inject+-lemma m i ⟩
      toℕ (inject+ m i)
        ≡⟨ P.cong toℕ inj≡ ⟩
      toℕ (raise n j)
        ≡⟨ toℕ-raise n j ⟩
      n N+ toℕ j
    ∎
    where
      open P.≡-Reasoning
      open import Data.Fin.Properties

  m⊎n↔m+n : ∀ {m n} →
            Bijection (P.setoid (Fin m ⊎ Fin n)) (P.setoid (Fin (m N+ n)))
  m⊎n↔m+n {m} {n} = record { to = to⟶ ; bijective = bijective }
    where
      open import Relation.Nullary
      open import Data.Nat.Properties
      open import Function.LeftInverse using (_RightInverseOf_)
      
      from→ : ∀ {m n} → Fin (m N+ n) → Fin m ⊎ Fin n
      from→ {m} {n} i with m N≤? toℕ i
      ... | yes m≤i = inj₂ (reduce≥ i m≤i)
      ... | no ¬m≤i = inj₁ (fromℕ≤ {toℕ i} (≰⇒> ¬m≤i))

      to→ : ∀ {m n} → Fin m ⊎ Fin n → Fin (m N+ n)
      to→ {m} {n} = [ inject+ n , raise m ]′

      from⟶ = P.→-to-⟶ from→
      to⟶ = P.→-to-⟶ to→

      injective : ∀ {i j : Fin m ⊎ Fin n} → to→ i ≡ to→ j → i ≡ j
      injective {inj₁ i′} {inj₁ j′} to→≡ = {!!}
      injective {inj₁ i′} {inj₂ j′} to→≡ = {!!}
      injective {inj₂ i′} {j} to→≡ = {!!}
--    injective {i⊎} {j⊎} tom≡ton with i⊎ | j⊎
--    ... | inj₁ i′ | inj₁ j′ = P.cong inj₁ (inject+k-injective {m} i′ j′ tom≡ton)
--    ... | inj₁ i′ | inj₂ j′ = {!inject+-raise-injective!}
--    ... | inj₂ i′ | inj₁ j′ = {!!}
--    ... | inj₂ i′ | inj₂ j′ = P.cong inj₂ (raisek-injective m i′ j′ tom≡ton)

      surjective : Surjective to⟶
      surjective = record { from = from⟶ ; right-inverse-of = right-inv }
        where
          right-inv : ∀ (k : Fin (m N+ n)) → to→ {m} {n} (from→ k) ≡ k -- from⟶ RightInverseOf to⟶
          right-inv k with m N≤? toℕ k | from→ {m} {n} k
          ... | m≤i | inj₁ k′  = {!!}
          ... | m≤i | inj₂ m-k = {!!}

      bijective : Bijective to⟶
      bijective = record { injective = injective ; surjective = surjective }
