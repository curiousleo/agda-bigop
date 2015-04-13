module Prototypes.SquareMatrixSemiring where

  open import Prototypes.Matrix
  open import Prototypes.BigopFold hiding (_…_)

  open import Algebra
  open import Algebra.FunctionProperties
  open import Algebra.Structures

  open import Data.Fin using (Fin)
  open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
  open import Data.Nat using (ℕ)
  open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry)
  import Data.Vec as V

  open import Function
  open import Function.Equivalence as Equiv using (_⇔_)

  open import Relation.Nullary
  open import Relation.Binary.Core hiding (refl)
  open import Relation.Binary
  import Relation.Binary.Vec.Pointwise as PW
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.SetoidReasoning as SetR
  
  record Pointwise {ℓ} {A B : Set ℓ} (_∼_ : REL A B ℓ)
                   {m n} (x : Matrix A m n) (y : Matrix B m n) : Set ℓ where
    constructor ext
    field app : ∀ r c → lookup r c x ∼ lookup r c y

  PW-equivalent : ∀ {ℓ} {A B : Set ℓ} {_~_ : REL A B ℓ} {m n}
                  {x : Matrix A m n} {y : Matrix B m n} →
                  PW.Pointwise (PW.Pointwise _~_) x y ⇔ Pointwise _~_ x y
  PW-equivalent {_~_ = _~_} {x = x} {y} = Equiv.equivalence to from
    where
      to : PW.Pointwise (PW.Pointwise _~_) x y → Pointwise _~_ x y
      to (PW.ext app) = ext cong
        where
          cong : ∀ r c → lookup r c x ~ lookup r c y
          cong r c with app r
          cong r c | PW.ext app′ = app′ c

      from : Pointwise _~_ x y → PW.Pointwise (PW.Pointwise _~_) x y
      from (ext app) = PW.ext (λ r → PW.ext (app r))

  module SquareMatrix (n : ℕ) {ℓ} (s : Semiring ℓ ℓ) where

    open Semiring s renaming (Carrier to A)
    open Core +-monoid using (Σ-syntax)
    open Core *-monoid using (Π-syntax)

    _…_ = fromLenF

    -----------------
    -- Definitions --
    -----------------

    M : ℕ → Set _
    M n = Matrix A n n

    mult : M n → M n → Fin n → Fin n → A
    mult x y r c = Σ[ i ← 0 … n $ x [ r , i ] * y [ i , c ] ]

    _≈M_ : Rel (M n) ℓ
    _≈M_ = Pointwise _≈_

    _+M_ : ∀ {n} → Op₂ (M n)
    x +M y = tabulate (λ r c → lookup r c x + lookup r c y)

    _*M_ : Op₂ (M n)
    x *M y = tabulate (mult x y)

    0M : M n
    0M = tabulate (λ r c → 0#)

    1M : M n
    1M = tabulate diag
      where
        diag : Fin n → Fin n → A
        diag r c with r ≟F c
        ... | yes _ = 1#
        ... | no  _ = 0#

    ------------
    -- Proofs --
    ------------

    ≈M-isEquivalence : IsEquivalence _≈M_
    ≈M-isEquivalence = record { refl = ≈M-refl ; sym = ≈M-sym ; trans = ≈M-trans }
      where
        ≈M-refl : Reflexive _≈M_
        ≈M-refl = ext (λ r c → refl)

        ≈M-sym : Symmetric _≈M_
        ≈M-sym (ext app) = ext (λ r c → sym (app r c))

        ≈M-trans : Transitive _≈M_
        ≈M-trans (ext app₁) (ext app₂) = ext (λ r c → trans (app₁ r c) (app₂ r c))

    lookup∘tabulate : ∀ (f : Fin n → Fin n → A) r c →
                      lookup r c (tabulate f) ≡ f r c
    lookup∘tabulate f r c =
      P.trans (P.cong (V.lookup c)
                      (l∘t (λ r → V.tabulate (f r)) r))
              (l∘t (f r) c)
      where
        open import Data.Vec.Properties using () renaming (lookup∘tabulate to l∘t)

    0M-lemma : ∀ r c → 0M [ r , c ] ≡ 0#
    0M-lemma = lookup∘tabulate _

    +M-assoc : Associative _≈M_ _+M_
    +M-assoc x y z = ext assoc
      where
        lookupM+ : ∀ {x y : M n} r c →
                   (x +M y) [ r , c ] ≡ x [ r , c ] + y [ r , c ]
        lookupM+ = lookup∘tabulate _

        factorₗ : ∀ r c →
                   ((x +M y) +M z) [ r , c ] ≡ (x [ r , c ] + y [ r , c ]) + z [ r , c ]
        factorₗ r c = begin
          ((x +M y) +M z) [ r , c ]         ≡⟨ lookupM+ r c ⟩
          (x +M y) [ r , c ] + z [ r , c ]  ≡⟨ P.cong₂ _+_ (lookupM+ r c) P.refl ⟩
          (x [ r , c ] + y [ r , c ]) + z [ r , c ] ∎
          where
            open P.≡-Reasoning

        factorᵣ : ∀ r c →
                   (x +M (y +M z)) [ r , c ] ≡ x [ r , c ] + (y [ r , c ] + z [ r , c ])
        factorᵣ r c = begin
          (x +M (y +M z)) [ r , c ]         ≡⟨ lookupM+ r c ⟩
          x [ r , c ] + (y +M z) [ r , c ]  ≡⟨ P.cong₂ _+_ P.refl (lookupM+ r c) ⟩
          x [ r , c ] + (y [ r , c ] + z [ r , c ]) ∎
          where
            open P.≡-Reasoning

        assoc : ∀ r c → ((x +M y) +M z) [ r , c ] ≈ (x +M (y +M z)) [ r , c ]
        assoc r c = begin⟨ setoid ⟩
          ((x +M y) +M z) [ r , c ]
            ≡⟨ factorₗ r c ⟩
          (x [ r , c ] + y [ r , c ]) + z [ r , c ]
            ≈⟨ +-assoc _ _ _ ⟩
          x [ r , c ] + (y [ r , c ] + z [ r , c ])
            ≡⟨ P.sym (factorᵣ r c) ⟩
          (x +M (y +M z)) [ r , c ] ∎
          where open SetR

    +M-cong : _+M_ Preserves₂ _≈M_ ⟶ _≈M_ ⟶ _≈M_
    +M-cong {u} {v} {x} {y} (ext app₁) (ext app₂) = ext cong
      where
        cong : ∀ r c → (u +M x) [ r , c ] ≈ (v +M y) [ r , c ]
        cong r c = begin⟨ setoid ⟩
          (u +M x) [ r , c ]         ≡⟨ lookup∘tabulate _ r c ⟩
          u [ r , c ] + x [ r , c ]  ≈⟨ +-cong (app₁ r c) (app₂ r c) ⟩
          v [ r , c ] + y [ r , c ]  ≡⟨ P.sym (lookup∘tabulate _ r c) ⟩
          (v +M y) [ r , c ] ∎
          where open SetR

    +M-identityˡ : LeftIdentity _≈M_ 0M _+M_
    +M-identityˡ x = ext ident
      where
        ident : ∀ r c → (0M +M x) [ r , c ] ≈ x [ r , c ]
        ident r c = begin⟨ setoid ⟩
          (0M +M x) [ r , c ]         ≡⟨ lookup∘tabulate _ r c ⟩
          0M [ r , c ] + x [ r , c ]  ≡⟨ P.cong₂ _+_ (lookup∘tabulate _ r c) P.refl ⟩
                    0# + x [ r , c ]  ≈⟨ identityˡ _ ⟩
                         x [ r , c ]  ∎
          where
            open SetR
            open IsCommutativeMonoid +-isCommutativeMonoid

    +M-comm : Commutative _≈M_ _+M_
    +M-comm x y = ext comm
      where
        comm : ∀ r c → (x +M y) [ r , c ] ≈ (y +M x) [ r , c ]
        comm r c = begin⟨ setoid ⟩
          (x +M y) [ r , c ]         ≡⟨ lookup∘tabulate _ r c ⟩
          x [ r , c ] + y [ r , c ]  ≈⟨ +-comm _ _ ⟩
          y [ r , c ] + x [ r , c ]  ≡⟨ P.sym (lookup∘tabulate _ r c) ⟩
          (y +M x) [ r , c ] ∎
          where open SetR

    zeroˡ : LeftZero _≈M_ 0M _*M_
    zeroˡ x = ext z
      where
        open SemiringWithoutOneLemmas semiringWithoutOne
        open MonoidLemmas +-monoid

        z : ∀ r c → (0M *M x) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin⟨ setoid ⟩
          (0M *M x) [ r , c ]                ≡⟨ lookup∘tabulate _ r c ⟩
          Σ[ i ← 0 … n $ 0M [ r , i ] * x [ i , c ] ]
            ≈⟨ Σ-cong″ (λ i → *-cong (reflexive (0M-lemma r i)) refl)
                       (P.refl {x = 0 … n}) ⟩
          Σ[ i ← 0 … n $ 0# * x [ i , c ] ]  ≈⟨ sym (Σ-distrˡ _ 0# (0 … n)) ⟩
          0# * Σ[ i ← 0 … n $ x [ i , c ] ]  ≈⟨ proj₁ zero _ ⟩
          0#                                 ≡⟨ P.sym (0M-lemma r c) ⟩
          0M [ r , c ] ∎
          where open SetR

    zeroʳ : RightZero _≈M_ 0M _*M_
    zeroʳ x = ext z
      where
        open SemiringWithoutOneLemmas semiringWithoutOne
        open MonoidLemmas +-monoid

        z : ∀ r c → (x *M 0M) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin⟨ setoid ⟩
          (x *M 0M) [ r , c ]                ≡⟨ lookup∘tabulate _ r c ⟩
          Σ[ i ← 0 … n $ x [ r , i ] * 0M [ i , c ] ]
            ≈⟨ Σ-cong′ (λ i → *-cong refl (reflexive (0M-lemma i c))) (0 … n) ⟩
          Σ[ i ← 0 … n $ x [ r , i ] * 0# ]  ≈⟨ sym (Σ-distrʳ _ 0# (0 … n)) ⟩
          Σ[ i ← 0 … n $ x [ r , i ] ] * 0#  ≈⟨ proj₂ zero _ ⟩
          0#                                 ≡⟨ P.sym (0M-lemma r c) ⟩
          0M [ r , c ] ∎
          where open SetR

    *M-assoc : Associative _≈M_ _*M_
    *M-assoc x y z = ext assoc
      where
        open SemiringWithoutOneLemmas semiringWithoutOne
        open CommutativeMonoidLemmas +-commutativeMonoid
        open MonoidLemmas +-monoid

        assoc : ∀ r c → ((x *M y) *M z) [ r , c ] ≈ (x *M (y *M z)) [ r , c ]
        assoc r c = begin⟨ setoid ⟩
          ((x *M y) *M z) [ r , c ]
            ≡⟨ lookup∘tabulate _ r c ⟩
          Σ[ i ← 0 … n $ (x *M y) [ r , i ] * z [ i , c ] ]
            ≈⟨ flip Σ-cong′ (0 … n) (λ i → begin⟨ setoid ⟩

              (x *M y) [ r , i ] * z [ i , c ]
                ≈⟨ *-cong (reflexive $ lookup∘tabulate _ r i) refl ⟩
              (Σ[ j ← 0 … n $ x [ r , j ] * y [ j , i ] ]) * z [ i , c ]
                ≈⟨ Σ-distrʳ _ _ (0 … n) ⟩
              Σ[ j ← 0 … n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ] ∎ ) ⟩

          Σ[ i ← 0 … n $ Σ[ j ← 0 … n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ] ]
            ≈⟨ Σ-swap _ (0 … n) (0 … n) ⟩
          Σ[ j ← 0 … n $ Σ[ i ← 0 … n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ] ]
            ≈⟨ flip Σ-cong′ (0 … n) (λ j → begin⟨ setoid ⟩

              Σ[ i ← 0 … n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ]
                ≈⟨ Σ-cong′ (λ i → *-assoc _ _ _) (0 … n) ⟩
              Σ[ i ← 0 … n $ x [ r , j ] * (y [ j , i ] * z [ i , c ]) ]
                ≈⟨ sym (Σ-distrˡ _ _ (0 … n)) ⟩
              x [ r , j ] * Σ[ i ← 0 … n $ y [ j , i ] * z [ i , c ] ]
                ≈⟨ *-cong refl (sym $ reflexive $ lookup∘tabulate _ j c) ⟩
              x [ r , j ] * (y *M z) [ j , c ] ∎ ) ⟩

          Σ[ j ← 0 … n $ x [ r , j ] * (y *M z) [ j , c ] ]
            ≡⟨ P.sym (lookup∘tabulate _ r c) ⟩
          (x *M (y *M z)) [ r , c ] ∎
          where open SetR

    *M-cong : _*M_ Preserves₂ _≈M_ ⟶ _≈M_ ⟶ _≈M_
    *M-cong {u} {v} {x} {y} (ext app₁) (ext app₂) = ext cong
      where
        open MonoidLemmas +-monoid

        cong : ∀ r c → (u *M x) [ r , c ] ≈ (v *M y) [ r , c ]
        cong r c = begin⟨ setoid ⟩
          (u *M x) [ r , c ]
            ≡⟨ lookup∘tabulate _ r c ⟩
          Σ[ i ← 0 … n $ u [ r , i ] * x [ i , c ] ]
            ≈⟨ Σ-cong′ (λ i → *-cong (app₁ r i) (app₂ i c)) (0 … n) ⟩
          Σ[ i ← 0 … n $ v [ r , i ] * y [ i , c ] ]
            ≡⟨ P.sym (lookup∘tabulate _ r c) ⟩
          (v *M y) [ r , c ] ∎
          where open SetR

    *M-identityˡ : LeftIdentity _≈M_ 1M _*M_
    *M-identityˡ x = ext {!!}

    *M-identityʳ : RightIdentity _≈M_ 1M _*M_
    *M-identityʳ x = ext {!!}

    *M-distrOverˡ-+M : (_≈M_ DistributesOverˡ _*M_) _+M_
    *M-distrOverˡ-+M x y z = ext {!!}

    *M-distrOverʳ-+M : (_≈M_ DistributesOverʳ _*M_) _+M_
    *M-distrOverʳ-+M x y z = ext {!!}

    M-isSemiring : IsSemiring _≈M_ _+M_ _*M_ 0M 1M
    M-isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isSemigroup = record
            { isEquivalence = ≈M-isEquivalence
            ; assoc         = +M-assoc
            ; ∙-cong        = +M-cong
            }
          ; identityˡ = +M-identityˡ
          ; comm = +M-comm
          }
        ; *-isMonoid = record
          { isSemigroup = record
            { isEquivalence = ≈M-isEquivalence
            ; assoc  = *M-assoc
            ; ∙-cong = *M-cong
            }
          ; identity = *M-identityˡ , *M-identityʳ
          }
        ; distrib = *M-distrOverˡ-+M , *M-distrOverʳ-+M
        }
      ; zero = zeroˡ , zeroʳ
      }
