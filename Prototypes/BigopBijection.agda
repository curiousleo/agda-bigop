module Prototypes.BigopBijection where

--  open import Primitive hiding (suc)

  open import Function.Bijection renaming (_∘_ to _∘B_; id to idB)
  open import Function.Surjection hiding (_∘_; id)
  open import Function using (id; _∘_)
  open import Data.Nat renaming (_+_ to _N+_ ; _≤_ to _N≤_ ; _≥_ to _N≥_ ; _≤?_ to _N≤?_)
  import Level as L
  open import Data.Fin
  import Relation.Binary.PropositionalEquality as P
  open import Relation.Binary
  open import Relation.Binary.Core using (_≡_)
  import Function as Fun
  import Data.Bool as Bool
  open import Data.Nat.Properties.Simple
  open import Data.Vec
  open import Data.Vec.Properties
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
      cmon         : IsCommutativeMonoid _≡_ _·_ ε

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


  FinFinType : {n : ℕ} → FinType {n} (Fin n)
  FinFinType = record { to = Fin⟶Nat ; bijective = bijective }
    where
      Fin⟶Nat = record { _⟨$⟩_ = Fun.id ; cong = Fun.id }
      bijective = record { injective = Fun.id ; surjective = surjective }
        where
          surjective = record { from = Fin⟶Nat ; right-inverse-of = right-inv }
            where
              right-inv = λ x → P.refl

  Sum : (n : ℕ) → Bigop
  Sum n = record
    { size = n ; Index = Fin n ; Result = ℕ
    ; index = FinFinType ; ε = zero ; _·_ = _N+_ ; cmon = cmon
    }
    where
      open import Data.Nat.Properties.Simple
      cmon : IsCommutativeMonoid _≡_ _N+_ zero
      cmon = record
        { isSemigroup = record
          { isEquivalence = P.isEquivalence
          ; assoc = +-assoc
          ; ∙-cong = P.cong₂ _N+_
          }
        ; identityˡ = λ x → P.refl
        ; comm = +-comm
        }

  Product : (n : ℕ) → Bigop
  Product n = record
    { size = n ; Index = Fin n ; Result = ℕ
    ; index = FinFinType ; ε = 1 ; _·_ = _*_ ; cmon = cmon
    }
    where
      open import Data.Nat.Properties.Simple
      cmon : IsCommutativeMonoid _≡_ _*_ 1
      cmon = record
        { isSemigroup = record
          { isEquivalence = P.isEquivalence
          ; assoc = *-assoc
          ; ∙-cong = P.cong₂ _*_
          }
        ; identityˡ = +-right-identity
        ; comm = *-comm
        }

  module BigopLemmas {i r} (bigop : Bigop {i} {r}) where
    open Bigop bigop
    import Algebra.FunctionProperties as FP
    open FP {A = Result} _≡_ hiding (Op₂)
    open import Data.Nat
    open import Data.Product hiding (map)
    open import Relation.Binary.PropositionalEquality
    open import Algebra
    import Relation.Binary.Vec.Pointwise as PW

    assoc : Associative _·_
    assoc = IsSemigroup.assoc (IsCommutativeMonoid.isSemigroup cmon)

    identity : Identity ε _·_
    identity = IsMonoid.identity (IsCommutativeMonoid.isMonoid cmon)

    idˡ : LeftIdentity ε _·_
    idˡ = proj₁ identity

    idʳ : RightIdentity ε _·_
    idʳ = proj₂ identity

    comm : Commutative _·_
    comm = IsCommutativeMonoid.comm cmon
{-
    tabulateʳ : ∀ {n} (f : Fin (suc n) → Result) → last (tabulate {suc n} f) ≡ f (fromℕ n)
    tabulateʳ {zero} f = refl
    tabulateʳ {suc n} f = {!!}
-}

    replicate-tabulate : ∀ {n a b c} {A : Set a} {B : Set b} {C : Set c}
                          (f : B → C) (g : A → B) (h : Fin n → A) →
                          replicate f ⊛ tabulate (g ∘ h) ≡ replicate (f ∘ g) ⊛ tabulate h
    replicate-tabulate {zero} f g h = refl
    replicate-tabulate {suc n} f g h
      rewrite
        replicate-tabulate f g (h ∘ suc) = refl

    foldl-elim : ∀ {a b c} {A : Set a} {B : ℕ → Set b}
                 (P : ∀ {n} → Vec A n → B n → Set c)
                 {f : ∀ {n} → B n → A → B (1 N+ n)} {z : B 0} →
                 P [] z →
                 (∀ {n x′ z′} {xs′ : Vec A n} → P xs′ z′ → P (xs′ ∷ʳ x′)
                                                             (f z′ x′)) →
                 ∀ {n} (xs : Vec A n) → P xs (foldl B f z xs)
    foldl-elim _ Pz _  []       = Pz
    foldl-elim P Pz Ps (x ∷ xs) =
      foldl-elim (λ xs′ → P (x ∷ xs′)) (Ps Pz) Ps xs

    foldr· : ∀ {m : ℕ} → Result → Vec Result m → Result
    foldr· = foldr (λ _ → Result) _·_

    foldl· : ∀ {m : ℕ} → Result → Vec Result m → Result
    foldl· = foldl (λ _ → Result) _·_

    foldl·-distr : ∀ {m} (x y : Result) (ys : Vec Result m) →
                   x · foldl· y ys ≡ foldl· (x · y) ys
    foldl·-distr x y [] = refl
    foldl·-distr x y (y′ ∷ ys)
      rewrite
        assoc x y y′ = foldl·-distr x (y · y′) ys

    foldl·-pickˡ : ∀ {m} (x y : Result) (ys : Vec Result m) →
                   x · foldl· y ys ≡ foldl· y (x ∷ ys)
    foldl·-pickˡ x y [] = comm x y
    foldl·-pickˡ x y (y′ ∷ ys)
      rewrite
        assoc y x y′ | comm x y′ | sym (assoc y y′ x) | comm (y · y′) x
        = foldl·-distr x (y · y′) ys

    foldl·-pickʳ : ∀ {m} (x y : Result) (ys : Vec Result m) →
                   foldl· y (ys ∷ʳ x) ≡ foldl· y ys · x
    foldl·-pickʳ _ _ [] = refl
    foldl·-pickʳ x y (y′ ∷ ys)
      rewrite
        foldl·-pickʳ x (y · y′) ys = refl

    foldl-foldr : ∀ {m} (x : Result) (xs : Vec Result m) →
                  foldr· x xs ≡ foldl· x xs
    foldl-foldr _ [] = refl
    foldl-foldr x (y ∷ ys)
      rewrite
        comm x y
      | foldl-foldr x ys = foldl·-distr y x ys

    initLast-∷ʳ : ∀ {m} {a} {A : Set a} (xs : Vec A m) (x : A) →
                  initLast (xs ∷ʳ x) ≡ (xs , x , refl)
    initLast-∷ʳ {zero}  []        _  = refl
    initLast-∷ʳ {suc m} (x₁ ∷ xs) x¹
      rewrite
        initLast-∷ʳ {m} xs x¹ = refl

    foldr·-lemmaˡ : ∀ {m : ℕ} (x y : Result) (ys : Vec Result m) →
                   foldr· x (y ∷ ys) ≡ y · foldr· x ys
    foldr·-lemmaˡ {zero}  _ _ []                                 = refl
    foldr·-lemmaˡ {suc m} _ y (y′ ∷ ys) rewrite foldr·-lemmaˡ y y′ ys = refl

    foldr·-lemmaʳ : ∀ {m : ℕ} (x : Result) (v : Vec Result (suc m)) →
                   foldr· x v ≡ foldr· x (init v) · last v
    foldr·-lemmaʳ {zero}  y (x ∷ []) = comm x y
    foldr·-lemmaʳ {suc m} y (x ∷ v) with initLast v
    foldr·-lemmaʳ {suc m} y (x ∷ .(v′ ∷ʳ x′)) | v′ , x′ , refl
      rewrite
        assoc x (foldr· y v′) x′
      | foldr·-lemmaʳ {m} y (v′ ∷ʳ x′)
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

    foldr·-map-lemmaˡ : ∀ {m} (x : Index) (y : Result) (xs : Vec Index m)
                       (f : Index → Result) →
                       foldr· y (map f (x ∷ xs)) ≡ f x · foldr· y (map f xs)
    foldr·-map-lemmaˡ x y xs f = foldr·-lemmaˡ y (f x) (map f xs)

    foldr·-map-lemmaʳ : ∀ {m} (x : Result) (v : Vec Index (suc m))
                        (f : Index → Result) →
                        foldr· x (map f v) ≡
                        foldr· x (init (map f v)) · f (last v)
    foldr·-map-lemmaʳ {m} x v f
      rewrite
        foldr·-lemmaʳ x (map f v)
      | last-map {v = v} f = refl
{-
    reverse-∷ʳ : ∀ {m} (x : Result) (xs : Vec Result m) →
                 reverse (x ∷ xs) ≡ (reverse xs) ∷ʳ x
    reverse-∷ʳ x [] = refl
    reverse-∷ʳ x (y ∷ ys) rewrite sym (foldl·-pickʳ x y ys) = {!!}

    foldr·-reverse : ∀ {m} (rs : Vec Result m) → foldr· ε rs ≡ foldr· ε (reverse rs)
    foldr·-reverse [] = refl
    foldr·-reverse (r ∷ rs) rewrite foldl·-pickˡ r ε rs = {!!}
-}
{-
    foldr·-enum-lemmaˡ : ∀ {m} → size ≡ suc m → (f : Index → Result) →
                        foldr·-map-lemmaˡ (enum index) f
    foldr·-enum-lemmaˡ = ?
-}
  _⟦_⟧ : ∀ {i r} → (o : Bigop {i} {r}) → (Bigop.Index o → Bigop.Result o) → (Bigop.Result o)
  _⟦_⟧ {i} {r} o f = foldr· ε (map f (enum index))
    where
      open Bigop o
      open BigopLemmas o

  Sum-lemma : ∀ {n} (f : ℕ → ℕ) →
              (Sum n) ⟦ suc ∘ f ∘ toℕ ⟧ ≡ n N+ (Sum n) ⟦ f ∘ toℕ ⟧
  Sum-lemma {zero} f = P.refl
  Sum-lemma {suc n} f
    rewrite
      P.sym (tabulate-∘ {n} (f ∘ toℕ) suc)
    | P.sym (tabulate-∘ {n} (Data.Nat.suc ∘ f ∘ toℕ) suc)
    | P.sym (+-assoc n (f 0) (foldr (λ _ → ℕ) {n} _N+_ 0 (tabulate (f ∘ Data.Nat.suc ∘ toℕ))))
    | +-comm n (f 0)
    | +-assoc (f 0) n (foldr (λ _ → ℕ) {n} _N+_ 0 (tabulate (f ∘ Data.Nat.suc ∘ toℕ)))
    | tabulate-∘ {n} (Data.Nat.suc ∘ f ∘ Data.Nat.suc ∘ toℕ) id
    | tabulate-∘ {n} (f ∘ Data.Nat.suc ∘ toℕ) id
    | Sum-lemma {n} (f ∘ Data.Nat.suc)
    = P.refl -- P.cong suc (P.cong (_N+_ (f 0)) (Sum-lemma {n} (f ∘ Data.Nat.suc)))

  Sum-lemma′ : ∀ {n} (f : ℕ → ℕ) →
               (Sum (suc n)) ⟦ f ∘ toℕ ⟧ ≡ (f n) N+ (Sum n) ⟦ f ∘ toℕ ⟧
  Sum-lemma′ {zero} f = P.refl
  Sum-lemma′ {suc n} f
    rewrite
      P.refl
    | P.sym (tabulate-∘ {n} (f ∘ toℕ) (Data.Fin.suc ∘ suc))
    | P.sym (tabulate-∘ {n} (f ∘ toℕ) Data.Fin.suc)
    | P.sym (+-assoc (f 0) (f 1) (foldr (λ _ → ℕ) {n} _N+_ 0 (tabulate (f ∘ Data.Nat.suc ∘ Data.Nat.suc ∘ toℕ))))
    | +-comm (f 0) (f 1)
    | +-assoc (f 1) (f 0) (foldr (λ _ → ℕ) {n} _N+_ 0 (tabulate (f ∘ Data.Nat.suc ∘ Data.Nat.suc ∘ toℕ)))
    | tabulate-∘ {n} (f ∘ Data.Nat.suc ∘ Data.Nat.suc ∘ toℕ) id
    | tabulate-∘ {n} (f ∘ Data.Nat.suc ∘ toℕ) id
    | P.sym (Sum-lemma′ {n} (f ∘ Data.Nat.suc))
    = {!Sum-lemma {n} f!}


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
