module SquareMatrixSemiringProof where

  open import Matrix
  open import Bigop

  open import Algebra
  open import Algebra.FunctionProperties
  open import Algebra.Structures
  open import Data.Empty
  open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
  open import Data.Fin.Properties using (bounded)
  import Data.List.Base as L using ([_])
  import Data.Nat.Base as N
  open N using (ℕ; z≤n) renaming (zero to zeroℕ; suc to sucℕ)
  open import Data.Product using (proj₁; proj₂; _,_; uncurry)
  open import Function
  open import Function.Equivalence as Equiv using (_⇔_)
  open import Level using (_⊔_)
  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary.Core using (_≡_; _≢_)
  open import Relation.Binary
  import Relation.Binary.Vec.Pointwise as PW
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.SetoidReasoning as SetR

  record Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
                   {m n} (x : Matrix A m n) (y : Matrix B m n) : Set (a ⊔ b ⊔ ℓ) where
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

  module SquareMatrix (n : ℕ) {c ℓ} (s : Semiring c ℓ) where

    open Semiring s renaming (Carrier to A)
    open Fold +-monoid using (Σ-syntax)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne
    open Props.Ordinals

    ι = fromLenF 0

    -----------------
    -- Definitions --
    -----------------

    M : ℕ → Set _
    M n = Matrix A n n

    mult : M n → M n → Fin n → Fin n → A
    mult x y r c = Σ[ i ← ι n $ x [ r , i ] * y [ i , c ] ]

    _≈M_ : Rel (M n) (c ⊔ ℓ)
    _≈M_ = Pointwise _≈_

    _+M_ : Op₂ (M n)
    x +M y = tabulate (λ r c → x [ r , c ] + y [ r , c ])

    _*M_ : Op₂ (M n)
    x *M y = tabulate (mult x y)

    0M : M n
    0M = tabulate (λ r c → 0#)

    diag : {n : ℕ} → Fin n → Fin n → A
    diag zeroF    zeroF    = 1#
    diag zeroF    (sucF c) = 0#
    diag (sucF r) zeroF    = 0#
    diag (sucF r) (sucF c) = diag r c

    1M : M n
    1M = tabulate diag

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

    l∘t : ∀ {f : Fin n → Fin n → A} r c →
          lookup r c (tabulate f) ≡ f r c
    l∘t {f} r c =
      P.trans (P.cong (V.lookup c)
                      (lookup∘tabulate (λ r → V.tabulate (f r)) r))
              (lookup∘tabulate (f r) c)
      where
        open import Data.Vec.Properties using (lookup∘tabulate)
        import Data.Vec as V using (lookup; tabulate)

    1M-diag : ∀ r c → r ≡ c → 1M [ r , c ] ≡ 1#
    1M-diag r .r P.refl = begin
      1M [ r , r ]  ≡⟨ l∘t r r ⟩
      diag r r      ≡⟨ diag-lemma r ⟩
      1#  ∎
      where
        open P.≡-Reasoning

        diag-lemma : ∀ {n} (r : Fin n) → diag r r ≡ 1#
        diag-lemma zeroF    = P.refl
        diag-lemma (sucF r) = diag-lemma r

    1M-∁-diag : ∀ r c → ∁ (_≡_ r) c → 1M [ r , c ] ≡ 0#
    1M-∁-diag r c eq with r ≟F c
    1M-∁-diag r .r ¬eq | yes P.refl = ⊥-elim (¬eq P.refl)
    1M-∁-diag r  c ¬eq | no  _      = begin
      1M [ r , c ]  ≡⟨ l∘t r c ⟩
      diag r c      ≡⟨ diag-lemma r c ¬eq ⟩
      0#  ∎
      where
        open P.≡-Reasoning

        suc-¬-lemma : ∀ {n} {r c : Fin n} → ¬ sucF r ≡ sucF c → ¬ r ≡ c
        suc-¬-lemma {r} ¬eq P.refl = ¬eq P.refl

        diag-lemma : ∀ {n} (r c : Fin n) → ¬ r ≡ c → diag r c ≡ 0#
        diag-lemma zeroF    zeroF    ¬eq = ⊥-elim (¬eq P.refl)
        diag-lemma zeroF    (sucF _) _   = P.refl
        diag-lemma (sucF r) zeroF    ¬eq = P.refl
        diag-lemma (sucF r) (sucF c) ¬eq = diag-lemma r c (suc-¬-lemma ¬eq)


    +M-assoc : Associative _≈M_ _+M_
    +M-assoc x y z = ext assoc
      where
        factorₗ : ∀ r c →
                   ((x +M y) +M z) [ r , c ] ≡ (x [ r , c ] + y [ r , c ]) + z [ r , c ]
        factorₗ r c = begin
          ((x +M y) +M z) [ r , c ]         ≡⟨ l∘t r c ⟩
          (x +M y) [ r , c ] + z [ r , c ]  ≡⟨ P.cong₂ _+_ (l∘t r c) P.refl ⟩
          (x [ r , c ] + y [ r , c ]) + z [ r , c ] ∎
          where
            open P.≡-Reasoning

        factorᵣ : ∀ r c →
                   (x +M (y +M z)) [ r , c ] ≡ x [ r , c ] + (y [ r , c ] + z [ r , c ])
        factorᵣ r c = begin
          (x +M (y +M z)) [ r , c ]         ≡⟨ l∘t r c ⟩
          x [ r , c ] + (y +M z) [ r , c ]  ≡⟨ P.cong₂ _+_ P.refl (l∘t r c) ⟩
          x [ r , c ] + (y [ r , c ] + z [ r , c ]) ∎
          where
            open P.≡-Reasoning

        assoc : ∀ r c → ((x +M y) +M z) [ r , c ] ≈ (x +M (y +M z)) [ r , c ]
        assoc r c = begin⟨ setoid ⟩
          ((x +M y) +M z) [ r , c ]                    ≡⟨ factorₗ r c ⟩
          (x [ r , c ] +  y [ r , c ]) + z [ r , c ]   ≈⟨ +-assoc _ _ _ ⟩
           x [ r , c ] + (y [ r , c ]  + z [ r , c ])  ≡⟨ P.sym (factorᵣ r c) ⟩
          (x +M (y +M z)) [ r , c ]                    ∎
          where open SetR

    +M-cong : _+M_ Preserves₂ _≈M_ ⟶ _≈M_ ⟶ _≈M_
    +M-cong {u} {v} {x} {y} (ext app₁) (ext app₂) = ext cong
      where
        cong : ∀ r c → (u +M x) [ r , c ] ≈ (v +M y) [ r , c ]
        cong r c = begin⟨ setoid ⟩
          (u +M x) [ r , c ]         ≡⟨ l∘t r c ⟩
          u [ r , c ] + x [ r , c ]  ≈⟨ +-cong (app₁ r c) (app₂ r c) ⟩
          v [ r , c ] + y [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
          (v +M y) [ r , c ] ∎
          where open SetR

    +M-identityˡ : LeftIdentity _≈M_ 0M _+M_
    +M-identityˡ x = ext ident
      where
        ident : ∀ r c → (0M +M x) [ r , c ] ≈ x [ r , c ]
        ident r c = begin⟨ setoid ⟩
          (0M +M x) [ r , c ]         ≡⟨ l∘t r c ⟩
          0M [ r , c ] + x [ r , c ]  ≡⟨ P.cong₂ _+_ (l∘t r c) P.refl ⟩
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
          (x +M y) [ r , c ]         ≡⟨ l∘t r c ⟩
          x [ r , c ] + y [ r , c ]  ≈⟨ +-comm _ _ ⟩
          y [ r , c ] + x [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
          (y +M x) [ r , c ] ∎
          where open SetR

    M-zeroˡ : LeftZero _≈M_ 0M _*M_
    M-zeroˡ x = ext z
      where
        z : ∀ r c → (0M *M x) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin⟨ setoid ⟩
          (0M *M x) [ r , c ]              ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ 0M [ r , i ] * x [ i , c ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n})
                      (λ i → *-cong (reflexive (l∘t r i)) refl) ⟩
          Σ[ i ← ι n $ 0# * x [ i , c ] ]  ≈⟨ sym (Σ.distrˡ _ 0# (ι n)) ⟩
          0# * Σ[ i ← ι n $ x [ i , c ] ]  ≈⟨ proj₁ zero _ ⟩
          0#                               ≡⟨ P.sym (l∘t r c) ⟩
          0M [ r , c ] ∎
          where open SetR

    M-zeroʳ : RightZero _≈M_ 0M _*M_
    M-zeroʳ x = ext z
      where
        z : ∀ r c → (x *M 0M) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin⟨ setoid ⟩
          (x *M 0M) [ r , c ]              ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ x [ r , i ] * 0M [ i , c ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n})
                      (λ i → *-cong refl (reflexive (l∘t i c))) ⟩
          Σ[ i ← ι n $ x [ r , i ] * 0# ]  ≈⟨ sym (Σ.distrʳ _ 0# (ι n)) ⟩
          Σ[ i ← ι n $ x [ r , i ] ] * 0#  ≈⟨ proj₂ zero _ ⟩
          0#                               ≡⟨ P.sym (l∘t r c) ⟩
          0M [ r , c ] ∎
          where open SetR

    *M-assoc : Associative _≈M_ _*M_
    *M-assoc x y z = ext assoc
      where
        assoc : ∀ r c → ((x *M y) *M z) [ r , c ] ≈ (x *M (y *M z)) [ r , c ]
        assoc r c = begin⟨ setoid ⟩
          ((x *M y) *M z) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ (x *M y) [ r , i ] * z [ i , c ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n}) (λ i → begin⟨ setoid ⟩

              (x *M y) [ r , i ] * z [ i , c ]
                ≈⟨ *-cong (reflexive $ l∘t r i) refl ⟩
              (Σ[ j ← ι n $ x [ r , j ] * y [ j , i ] ]) * z [ i , c ]
                ≈⟨ Σ.distrʳ _ _ (ι n) ⟩
              Σ[ j ← ι n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ] ∎ ) ⟩

          Σ[ i ← ι n $ Σ[ j ← ι n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ] ]
            ≈⟨ Σ.swap _ (ι n) (ι n) ⟩
          Σ[ j ← ι n $ Σ[ i ← ι n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n}) (λ j → begin⟨ setoid ⟩

              Σ[ i ← ι n $ (x [ r , j ] * y [ j , i ]) * z [ i , c ] ]
                ≈⟨ Σ.cong (P.refl {x = ι n}) (λ i → *-assoc _ _ _) ⟩
              Σ[ i ← ι n $ x [ r , j ] * (y [ j , i ] * z [ i , c ]) ]
                ≈⟨ sym (Σ.distrˡ _ _ (ι n)) ⟩
              x [ r , j ] * Σ[ i ← ι n $ y [ j , i ] * z [ i , c ] ]
                ≈⟨ *-cong refl (sym $ reflexive $ l∘t j c) ⟩
              x [ r , j ] * (y *M z) [ j , c ] ∎ ) ⟩

          Σ[ j ← ι n $ x [ r , j ] * (y *M z) [ j , c ] ]
            ≡⟨ P.sym (l∘t r c) ⟩
          (x *M (y *M z)) [ r , c ] ∎
          where open SetR

    *M-cong : _*M_ Preserves₂ _≈M_ ⟶ _≈M_ ⟶ _≈M_
    *M-cong {u} {v} {x} {y} (ext app₁) (ext app₂) = ext cong
      where
        cong : ∀ r c → (u *M x) [ r , c ] ≈ (v *M y) [ r , c ]
        cong r c = begin⟨ setoid ⟩
          (u *M x) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ u [ r , i ] * x [ i , c ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n}) (λ i → *-cong (app₁ r i) (app₂ i c)) ⟩
          Σ[ i ← ι n $ v [ r , i ] * y [ i , c ] ]
            ≡⟨ P.sym (l∘t r c) ⟩
          (v *M y) [ r , c ] ∎
          where open SetR

    *M-identityˡ : LeftIdentity _≈M_ 1M _*M_
    *M-identityˡ x = ext ident
      where
        ident : ∀ r c → (1M *M x) [ r , c ] ≈ x [ r , c ]
        ident r c = begin⟨ setoid ⟩
          (1M *M x) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ 1M [ r , i ] * x [ i , c ] ]
            ≈⟨ Σ.split-P _ (ι n) (_≟F_ r) ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) $ 1M [ r , i ] * x [ i , c ] ] +
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ r) $ 1M [ r , i ] * x [ i , c ] ]
            ≈⟨ +-cong (Σ.cong-P (ι n) (_≟F_ r)
                                (λ i r≡i → *-cong (reflexive (1M-diag r i r≡i)) refl))
                      (Σ.cong-P (ι n) (∁-dec (_≟F_ r))
                                (λ i r≢i → *-cong (reflexive (1M-∁-diag r i r≢i)) refl)) ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) $ 1# * x [ i , c ] ] +
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ r) $ 0# * x [ i , c ] ]
            ≈⟨ sym $ +-cong (Σ.distrˡ _ 1# (ι n ∥ (_≟F_ r)))
                            (Σ.distrˡ _ 0# (ι n ∥ ∁-dec (_≟F_ r))) ⟩
          1# * Σ[ i ← ι n ∥ (_≟F_ r) $ x [ i , c ] ] +
          0# * Σ[ i ← ι n ∥ (∁-dec (_≟F_ r)) $ x [ i , c ] ]
            ≈⟨ +-cong (proj₁ *-identity _) (proj₁ zero _) ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) $ x [ i , c ] ] + 0#
            ≈⟨ proj₂ +-identity _ ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) $ x [ i , c ] ]
            ≡⟨ P.cong (Σ-syntax (λ i → x [ i , c ]))
                      (ordinals-filterF z≤n (bounded r)) ⟩
          Σ[ i ← L.[ r ] $ x [ i , c ] ]
            ≈⟨ proj₂ +-identity _  ⟩
          x [ r , c ] ∎
          where open SetR

    *M-identityʳ : RightIdentity _≈M_ 1M _*M_
    *M-identityʳ x = ext ident
      where
        ∁-sym : ∀ {a} {A : Set a} {x y : A} → ∁ (_≡_ x) y → ∁ (λ z → y ≡ z) x
        ∁-sym eq P.refl = eq P.refl

        ident : ∀ r c → (x *M 1M) [ r , c ] ≈ x [ r , c ]
        ident r c = begin⟨ setoid ⟩
          (x *M 1M) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ x [ r , i ] * 1M [ i , c ] ]
            ≈⟨ Σ.split-P _ (ι n) (_≟F_ c) ⟩
          Σ[ i ← ι n ∥ (_≟F_ c) $ x [ r , i ] * 1M [ i , c ] ] +
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ c) $ x [ r , i ] * 1M [ i , c ] ]
            ≈⟨ +-cong
                 (Σ.cong-P (ι n) (_≟F_ c)
                           (λ i c≡i → *-cong refl
                                             (reflexive (1M-diag i c (P.sym c≡i)))))
                 (Σ.cong-P (ι n) (∁-dec (_≟F_ c))
                           (λ i c≢i → *-cong refl
                                             (reflexive (1M-∁-diag i c (∁-sym c≢i))))) ⟩
          Σ[ i ← ι n ∥ (_≟F_ c) $ x [ r , i ] * 1# ] +
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ c) $ x [ r , i ] * 0# ]
            ≈⟨ sym $ +-cong (Σ.distrʳ _ 1# (ι n ∥ (_≟F_ c)))
                            (Σ.distrʳ _ 0# (ι n ∥ ∁-dec (_≟F_ c))) ⟩
          Σ[ i ← ι n ∥ (_≟F_ c) $ x [ r , i ] ] * 1# +
          Σ[ i ← ι n ∥ (∁-dec (_≟F_ c)) $ x [ r , i ] ] * 0#
            ≈⟨ +-cong (proj₂ *-identity _) (proj₂ zero _) ⟩
          Σ[ i ← ι n ∥ (_≟F_ c) $ x [ r , i ] ] + 0#
            ≈⟨ proj₂ +-identity _ ⟩
          Σ[ i ← ι n ∥ (_≟F_ c) $ x [ r , i ] ]
            ≡⟨ P.cong (Σ-syntax (λ i → x [ r , i ]))
                      (ordinals-filterF z≤n (bounded c)) ⟩
          Σ[ i ← L.[ c ] $ x [ r , i ] ]
            ≈⟨ proj₂ +-identity _  ⟩
          x [ r , c ] ∎
          where open SetR

    *M-distrOverˡ-+M : (_≈M_ DistributesOverˡ _*M_) _+M_
    *M-distrOverˡ-+M x y z = ext distr
      where
        distr : ∀ r c → (x *M (y +M z)) [ r , c ] ≈ ((x *M y) +M (x *M z)) [ r , c ]
        distr r c = begin⟨ setoid ⟩
          (x *M (y +M z)) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ x [ r , i ] * (y +M z) [ i , c ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n}) (λ i → begin⟨ setoid ⟩
              x [ r , i ] * (y +M z) [ i , c ]
                ≈⟨ *-cong refl (reflexive (l∘t i c)) ⟩
              x [ r , i ] * (y [ i , c ] + z [ i , c ])
                ≈⟨ proj₁ distrib _ _ _ ⟩
              (x [ r , i ] * y [ i , c ]) + (x [ r , i ] * z [ i , c ]) ∎)⟩
          Σ[ i ← ι n $ (x [ r , i ] * y [ i , c ]) + (x [ r , i ] * z [ i , c ]) ]
            ≈⟨ sym (Σ.split _ _ (ι n)) ⟩
          Σ[ i ← ι n $ x [ r , i ] * y [ i , c ] ] +
          Σ[ i ← ι n $ x [ r , i ] * z [ i , c ] ]
            ≡⟨ P.sym $ P.cong₂ _+_ (l∘t r c) (l∘t r c) ⟩
          (x *M y) [ r , c ] + (x *M z) [ r , c ]
            ≡⟨ P.sym (l∘t r c) ⟩
          ((x *M y) +M (x *M z)) [ r , c ] ∎
          where open SetR

    *M-distrOverʳ-+M : (_≈M_ DistributesOverʳ _*M_) _+M_
    *M-distrOverʳ-+M z x y = ext distr
      where
        distr : ∀ r c → ((x +M y) *M z) [ r , c ] ≈ ((x *M z) +M (y *M z)) [ r , c ]
        distr r c = begin⟨ setoid ⟩
          ((x +M y) *M z) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n $ (x +M y) [ r , i ] * z [ i , c ] ]
            ≈⟨ Σ.cong (P.refl {x = ι n}) (λ i → begin⟨ setoid ⟩
              (x +M y) [ r , i ] * z [ i , c ]
                ≈⟨ *-cong (reflexive (l∘t r i)) refl ⟩
              (x [ r , i ] + y [ r , i ]) * z [ i , c ]
                ≈⟨ proj₂ distrib _ _ _ ⟩
              (x [ r , i ] * z [ i , c ]) + (y [ r , i ] * z [ i , c ]) ∎)⟩
          Σ[ i ← ι n $ (x [ r , i ] * z [ i , c ]) + (y [ r , i ] * z [ i , c ]) ]
            ≈⟨ sym (Σ.split _ _ (ι n)) ⟩
          Σ[ i ← ι n $ x [ r , i ] * z [ i , c ] ] +
          Σ[ i ← ι n $ y [ r , i ] * z [ i , c ] ]
            ≡⟨ P.sym $ P.cong₂ _+_ (l∘t r c) (l∘t r c) ⟩
          (x *M z) [ r , c ] + (y *M z) [ r , c ]
            ≡⟨ P.sym (l∘t r c) ⟩
          ((x *M z) +M (y *M z)) [ r , c ] ∎
          where open SetR

    ------------------------
    -- It's a … semiring! --
    ------------------------

    M-isSemiring : IsSemiring _≈M_ _+M_ _*M_ 0M 1M
    M-isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isSemigroup = record
            { isEquivalence = ≈M-isEquivalence
            ; assoc         = +M-assoc
            ; ∙-cong        = +M-cong
            }
          ; identityˡ       = +M-identityˡ
          ; comm            = +M-comm
          }
        ; *-isMonoid = record
          { isSemigroup = record
            { isEquivalence = ≈M-isEquivalence
            ; assoc         = *M-assoc
            ; ∙-cong        = *M-cong
            }
          ; identity        = *M-identityˡ , *M-identityʳ
          }
        ; distrib           = *M-distrOverˡ-+M , *M-distrOverʳ-+M
        }
      ; zero                = M-zeroˡ , M-zeroʳ
      }
