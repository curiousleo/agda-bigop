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
  open N using (ℕ; z≤n)
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

  record Pointwise {s t ℓ} {S : Set s} {T : Set t} (_∼_ : REL S T ℓ)
                   {m n} (A : Matrix S m n) (B : Matrix T m n) : Set (s ⊔ t ⊔ ℓ) where
    constructor ext
    field app : ∀ r c → A [ r , c ] ∼ B [ r , c ]

  PW-equivalent : ∀ {ℓ} {S T : Set ℓ} {_~_ : REL S T ℓ} {m n}
                  {A : Matrix S m n} {B : Matrix T m n} →
                  PW.Pointwise (PW.Pointwise _~_) A B ⇔ Pointwise _~_ A B
  PW-equivalent {_~_ = _~_} {A = A} {B} = Equiv.equivalence to from
    where
      to : PW.Pointwise (PW.Pointwise _~_) A B → Pointwise _~_ A B
      to (PW.ext app) = ext cong
        where
          cong : ∀ r c → A [ r , c ] ~ B [ r , c ]
          cong r c with app r
          cong r c | PW.ext app′ = app′ c

      from : Pointwise _~_ A B → PW.Pointwise (PW.Pointwise _~_) A B
      from (ext app) = PW.ext (λ r → PW.ext (app r))

  module SquareMatrix (n : ℕ) {c ℓ} (semiring : Semiring c ℓ) where

    open Semiring semiring
      using (Carrier;
             0#; 1#; _+_; _*_;
             setoid;
             +-semigroup; +-monoid; +-commutativeMonoid;
             *-semigroup; *-monoid;
             semiringWithoutOne)

    open Setoid setoid using (_≈_; refl; sym; trans; reflexive)

    open Fold +-monoid using (Σ-syntax)
    open Props.Ordinals

    open import Relation.Binary.EqReasoning setoid
    open P.≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)

    ι = fromLenF 0

    -----------------
    -- Definitions --
    -----------------

    M : Set c
    M = Matrix Carrier n n

    _≋_ : Rel M (c ⊔ ℓ)
    _≋_ = Pointwise _≈_

    _⊕_ : Op₂ M
    A ⊕ B = tabulate (λ r c → A [ r , c ] + B [ r , c ])

    mult : M → M → Fin n → Fin n → Carrier
    mult A B r c = Σ[ i ← ι n ] A [ r , i ] * B [ i , c ]

    _⊗_ : Op₂ M
    A ⊗ B = tabulate (mult A B)

    0M : M
    0M = tabulate (λ r c → 0#)

    diag : {n : ℕ} → Fin n → Fin n → Carrier
    diag zeroF    zeroF    = 1#
    diag zeroF    (sucF c) = 0#
    diag (sucF r) zeroF    = 0#
    diag (sucF r) (sucF c) = diag r c

    1M : M
    1M = tabulate diag

    ----------------------
    -- Auxiliary lemmas --
    ----------------------

    l∘t = lookup∘tabulate

    1M-diag : ∀ {r c} → r ≡ c → 1M [ r , c ] ≡ 1#
    1M-diag {r} {.r} P.refl = start
      1M [ r , r ]  ≣⟨ l∘t r r ⟩
      diag r r      ≣⟨ diag-lemma r ⟩
      1#            □
        where

        diag-lemma : ∀ {n} (r : Fin n) → diag r r ≡ 1#
        diag-lemma zeroF    = P.refl
        diag-lemma (sucF r) = diag-lemma r

    1M-∁-diag : ∀ {r c} → ∁ (_≡_ r) c → 1M [ r , c ] ≡ 0#
    1M-∁-diag {r} {c}   eq with ≟ r c
    1M-∁-diag {r} {.r} ¬eq | yes P.refl = ⊥-elim (¬eq P.refl)
    1M-∁-diag {r} {c}  ¬eq | no  _      = start
      1M [ r , c ]  ≣⟨ l∘t r c ⟩
      diag r c      ≣⟨ diag-lemma r c ¬eq ⟩
      0#            □
        where

        suc-¬-lemma : ∀ {n} {r c : Fin n} → ¬ sucF r ≡ sucF c → ¬ r ≡ c
        suc-¬-lemma {r} ¬eq P.refl = ¬eq P.refl

        diag-lemma : ∀ {n} (r c : Fin n) → ¬ r ≡ c → diag r c ≡ 0#
        diag-lemma zeroF    zeroF    ¬eq = ⊥-elim (¬eq P.refl)
        diag-lemma zeroF    (sucF _) _   = P.refl
        diag-lemma (sucF r) zeroF    ¬eq = P.refl
        diag-lemma (sucF r) (sucF c) ¬eq = diag-lemma r c (suc-¬-lemma ¬eq)

    ------------
    -- Proofs --
    ------------

    ≋-isEquivalence : IsEquivalence _≋_
    ≋-isEquivalence = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }
      where
        ≋-refl : Reflexive _≋_
        ≋-refl = ext (λ r c → refl)

        ≋-sym : Symmetric _≋_
        ≋-sym (ext app) = ext (λ r c → sym (app r c))

        ≋-trans : Transitive _≋_
        ≋-trans (ext app₁) (ext app₂) = ext (λ r c → trans (app₁ r c) (app₂ r c))

    ⊕-assoc : Associative _≋_ _⊕_
    ⊕-assoc A B C = ext assoc
      where
        open Semigroup +-semigroup using () renaming (assoc to +-assoc)

        factorₗ : ∀ r c →
                  ((A ⊕ B) ⊕ C) [ r , c ] ≡ (A [ r , c ] + B [ r , c ]) + C [ r , c ]
        factorₗ r c = start
          ((A ⊕ B) ⊕ C) [ r , c ]         ≣⟨ l∘t r c ⟩
          (A ⊕ B) [ r , c ] + C [ r , c ]  ≣⟨ P.cong₂ _+_ (l∘t r c) P.refl ⟩
          (A [ r , c ] + B [ r , c ]) + C [ r , c ] □

        factorᵣ : ∀ r c →
                  (A ⊕ (B ⊕ C)) [ r , c ] ≡ A [ r , c ] + (B [ r , c ] + C [ r , c ])
        factorᵣ r c = start
          (A ⊕ (B ⊕ C)) [ r , c ]         ≣⟨ l∘t r c ⟩
          A [ r , c ] + (B ⊕ C) [ r , c ]  ≣⟨ P.cong₂ _+_ P.refl (l∘t r c) ⟩
          A [ r , c ] + (B [ r , c ] + C [ r , c ]) □

        assoc : ∀ r c → ((A ⊕ B) ⊕ C) [ r , c ] ≈ (A ⊕ (B ⊕ C)) [ r , c ]
        assoc r c = begin
          ((A ⊕ B) ⊕ C) [ r , c ]                    ≡⟨ factorₗ r c ⟩
          (A [ r , c ] +  B [ r , c ]) + C [ r , c ]   ≈⟨ +-assoc _ _ _ ⟩
           A [ r , c ] + (B [ r , c ]  + C [ r , c ])  ≡⟨ P.sym (factorᵣ r c) ⟩
          (A ⊕ (B ⊕ C)) [ r , c ]                    ∎

    ⊕-cong : _⊕_ Preserves₂ _≋_ ⟶ _≋_ ⟶ _≋_
    ⊕-cong {A} {A′} {B} {B′} (ext app₁) (ext app₂) = ext cong
      where
        open Semigroup +-semigroup using () renaming (∙-cong to +-cong)

        cong : ∀ r c → (A ⊕ B) [ r , c ] ≈ (A′ ⊕ B′) [ r , c ]
        cong r c = begin
          (A ⊕ B) [ r , c ]            ≡⟨ l∘t r c ⟩
          A [ r , c ] + B [ r , c ]    ≈⟨ +-cong (app₁ r c) (app₂ r c) ⟩
          A′ [ r , c ] + B′ [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
          (A′ ⊕ B′) [ r , c ]          ∎

    ⊕-identityˡ : LeftIdentity _≋_ 0M _⊕_
    ⊕-identityˡ A = ext ident
      where
        open Monoid +-monoid using () renaming (identity to +-identity)

        ident : ∀ r c → (0M ⊕ A) [ r , c ] ≈ A [ r , c ]
        ident r c = begin
          (0M ⊕ A) [ r , c ]         ≡⟨ l∘t r c ⟩
          0M [ r , c ] + A [ r , c ]  ≡⟨ P.cong₂ _+_ (l∘t r c) P.refl ⟩
                    0# + A [ r , c ]  ≈⟨ proj₁ +-identity _ ⟩
                         A [ r , c ]  ∎

    ⊕-comm : Commutative _≋_ _⊕_
    ⊕-comm A B = ext comm
      where
        open CommutativeMonoid +-commutativeMonoid using () renaming (comm to +-comm)

        comm : ∀ r c → (A ⊕ B) [ r , c ] ≈ (B ⊕ A) [ r , c ]
        comm r c = begin
          (A ⊕ B) [ r , c ]         ≡⟨ l∘t r c ⟩
          A [ r , c ] + B [ r , c ]  ≈⟨ +-comm _ _ ⟩
          B [ r , c ] + A [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
          (B ⊕ A) [ r , c ] ∎

    M-zeroˡ : LeftZero _≋_ 0M _⊗_
    M-zeroˡ A = ext z
      where
        open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne

        z : ∀ r c → (0M ⊗ A) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin
          (0M ⊗ A) [ r , c ]              ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] 0M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl
                      (λ i → *-cong (reflexive (l∘t r i)) refl) ⟩
          Σ[ i ← ι n ] 0# * A [ i , c ]  ≈⟨ sym (Σ.distrˡ _ 0# (ι n)) ⟩
          0# * (Σ[ i ← ι n ] A [ i , c ])  ≈⟨ proj₁ zero _ ⟩
          0#                               ≡⟨ P.sym (l∘t r c) ⟩
          0M [ r , c ] ∎

    M-zeroʳ : RightZero _≋_ 0M _⊗_
    M-zeroʳ A = ext z
      where
        open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne

        z : ∀ r c → (A ⊗ 0M) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin
          (A ⊗ 0M) [ r , c ]              ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] A [ r , i ] * 0M [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl
                      (λ i → *-cong refl (reflexive (l∘t i c))) ⟩
          Σ[ i ← ι n ] A [ r , i ] * 0#  ≈⟨ sym (Σ.distrʳ _ 0# (ι n)) ⟩
          (Σ[ i ← ι n ] A [ r , i ]) * 0#  ≈⟨ proj₂ zero _ ⟩
          0#                               ≡⟨ P.sym (l∘t r c) ⟩
          0M [ r , c ] ∎

    ⊗-assoc : Associative _≋_ _⊗_
    ⊗-assoc A B C = ext assoc
      where
        open SemiringWithoutOne semiringWithoutOne using (*-assoc; *-cong)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne

        factorˡ : ∀ r c →
                  ((A ⊗ B) ⊗ C) [ r , c ] ≈
                  Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
        factorˡ r c = begin
          ((A ⊗ B) ⊗ C) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] (A ⊗ B) [ r , i ] * C [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (λ i → *-cong (reflexive (l∘t r i)) refl) ⟩
          Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ] ∎

        factorʳ : ∀ r c →
                  (A ⊗ (B ⊗ C)) [ r , c ] ≈
                  Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])
        factorʳ r c = begin
          (A ⊗ (B ⊗ C)) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ j ← ι n ] A [ r , j ] * (B ⊗ C) [ j , c ]
            ≈⟨ Σ.cong (ι n) P.refl (λ j → *-cong refl (reflexive (l∘t j c))) ⟩
          Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ]) ∎

        inner : ∀ r c j →
                Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ] ≈
                A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])
        inner r c j = begin
          Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (λ i → *-assoc _ _ _) ⟩
          Σ[ i ← ι n ] A [ r , j ] * (B [ j , i ] * C [ i , c ])
            ≈⟨ sym (Σ.distrˡ _ _ (ι n)) ⟩
          A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ]) ∎

        assoc : ∀ r c → ((A ⊗ B) ⊗ C) [ r , c ] ≈ (A ⊗ (B ⊗ C)) [ r , c ]
        assoc r c = begin
          ((A ⊗ B) ⊗ C) [ r , c ]
            ≈⟨ factorˡ r c ⟩
          Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (λ i → Σ.distrʳ _ _ (ι n)) ⟩
          Σ[ i ← ι n ] Σ[ j ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
            ≈⟨ Σ.swap _ (ι n) (ι n) ⟩
          Σ[ j ← ι n ] Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (inner r c) ⟩
          Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])
            ≈⟨ sym $ factorʳ r c ⟩
          (A ⊗ (B ⊗ C)) [ r , c ] ∎

    ⊗-cong : _⊗_ Preserves₂ _≋_ ⟶ _≋_ ⟶ _≋_
    ⊗-cong {u} {v} {A} {B} (ext app₁) (ext app₂) = ext cong
      where
        open Semigroup *-semigroup using () renaming (∙-cong to *-cong)
        module Σ = Props.Monoid +-monoid

        cong : ∀ r c → (u ⊗ A) [ r , c ] ≈ (v ⊗ B) [ r , c ]
        cong r c = begin
          (u ⊗ A) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] u [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (λ i → *-cong (app₁ r i) (app₂ i c)) ⟩
          Σ[ i ← ι n ] v [ r , i ] * B [ i , c ]
            ≡⟨ P.sym (l∘t r c) ⟩
          (v ⊗ B) [ r , c ] ∎

    ⊗-identityˡ : LeftIdentity _≋_ 1M _⊗_
    ⊗-identityˡ A = ext ident
      where
        open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne
          using (cong-P; split-P; distrˡ)

        ≡-step : ∀ r c →  Σ[ i ← ι n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ] ≈
                          Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]
        ≡-step r c = begin
          Σ[ i ← ι n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong-P  (ι n) (≟ r)
                         (λ i r≡i → reflexive (1M-diag r≡i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← ι n ∥ ≟ r ] 1# * A [ i , c ]    ≈⟨ sym $ Σ.distrˡ _ 1# (ι n ∥ ≟ r) ⟩
          1# * (Σ[ i ← ι n ∥ ≟ r ] A [ i , c ])  ≈⟨ proj₁ *-identity _ ⟩
          Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]         ∎

        ≢-step : ∀ r c → Σ[ i ← ι n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ] ≈ 0#
        ≢-step r c = begin
          Σ[ i ← ι n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong-P  (ι n) (∁′ (≟ r))
                         (λ i r≢i → reflexive (1M-∁-diag r≢i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← ι n ∥ ∁′ (≟ r) ] 0# * A [ i , c ]      ≈⟨ sym $ Σ.distrˡ _ 0# (ι n ∥ ∁′ (≟ r)) ⟩
          0# * (Σ[ i ← ι n ∥ (∁′ (≟ r)) ] A [ i , c ])  ≈⟨ proj₁ zero _ ⟩
          0#                                            ∎

        filter : ∀ r c → ι n ∥ ≟ r ≡ L.[ r ]
        filter r c = ordinals-filterF z≤n (bounded r)

        ident : ∀ r c → (1M ⊗ A) [ r , c ] ≈ A [ r , c ]
        ident r c = begin
          (1M ⊗ A) [ r , c ]                                     ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] 1M [ r , i ] * A [ i , c ]                ≈⟨ Σ.split-P _ (ι n) (≟ r) ⟩
          Σ[ i ← ι n ∥ ≟ r ]       1M [ r , i ] * A [ i , c ] +
          Σ[ i ← ι n ∥ ∁′ (≟ r) ]  1M [ r , i ] * A [ i , c ]    ≈⟨ ≡-step r c ⟨ +-cong ⟩ ≢-step r c ⟩
          Σ[ i ← ι n ∥ ≟ r ] A [ i , c ] + 0#                    ≈⟨ proj₂ +-identity _ ⟩
          Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]                         ≡⟨ P.cong  (Σ-syntax (λ i → A [ i , c ]))
                                                                            (filter r c) ⟩
          A [ r , c ] + 0#                                       ≈⟨ proj₂ +-identity _  ⟩
          A [ r , c ]                                            ∎

    ⊗-identityʳ : RightIdentity _≋_ 1M _⊗_
    ⊗-identityʳ A = ext ident
      where
        open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne

        ∁-sym : ∀ {a} {A : Set a} {A B : A} → ∁ (_≡_ A) B → ∁ (λ C → B ≡ C) A
        ∁-sym eq P.refl = eq P.refl

        ident : ∀ r c → (A ⊗ 1M) [ r , c ] ≈ A [ r , c ]
        ident r c = begin
          (A ⊗ 1M) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] A [ r , i ] * 1M [ i , c ]
            ≈⟨ Σ.split-P _ (ι n) (≟ c) ⟩
          Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ] * 1M [ i , c ] +
          Σ[ i ← ι n ∥ ∁′ (≟ c) ] A [ r , i ] * 1M [ i , c ]
            ≈⟨ +-cong
                 (Σ.cong-P (ι n) (≟ c)
                           (λ i c≡i → *-cong refl
                                             (reflexive (1M-diag (P.sym c≡i)))))
                 (Σ.cong-P (ι n) (∁′ (≟ c))
                           (λ i c≢i → *-cong refl
                                             (reflexive (1M-∁-diag (∁-sym c≢i))))) ⟩
          Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ] * 1# +
          Σ[ i ← ι n ∥ ∁′ (≟ c) ] A [ r , i ] * 0#
            ≈⟨ sym $ +-cong (Σ.distrʳ _ 1# (ι n ∥ (≟ c)))
                            (Σ.distrʳ _ 0# (ι n ∥ ∁′ (≟ c))) ⟩
          (Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ]) * 1# +
          (Σ[ i ← ι n ∥ (∁′ (≟ c)) ] A [ r , i ]) * 0#
            ≈⟨ +-cong (proj₂ *-identity _) (proj₂ zero _) ⟩
          (Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ]) + 0#
            ≈⟨ proj₂ +-identity _ ⟩
          Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ]
            ≡⟨ P.cong (Σ-syntax (λ i → A [ r , i ]))
                      (ordinals-filterF z≤n (bounded c)) ⟩
          Σ[ i ← L.[ c ] ] A [ r , i ]
            ≈⟨ proj₂ +-identity _  ⟩
          A [ r , c ] ∎

    ⊗-distrOverˡ-⊕ : (_≋_ DistributesOverˡ _⊗_) _⊕_
    ⊗-distrOverˡ-⊕ A B C = ext distr
      where
        open Semiring semiring using (*-cong; distrib)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne

        inner : ∀ r c i → A [ r , i ] * (B ⊕ C) [ i , c ] ≈
                          A [ r , i ] * B [ i , c ] + A [ r , i ] * C [ i , c ]
        inner r c i = begin
          A [ r , i ] * (B ⊕ C) [ i , c ]
            ≈⟨ *-cong refl (reflexive (l∘t i c)) ⟩
          A [ r , i ] * (B [ i , c ] + C [ i , c ])
            ≈⟨ proj₁ distrib _ _ _ ⟩
          (A [ r , i ] * B [ i , c ]) + (A [ r , i ] * C [ i , c ]) ∎

        distr : ∀ r c → (A ⊗ (B ⊕ C)) [ r , c ] ≈ ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ]
        distr r c = begin
          (A ⊗ (B ⊕ C)) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] A [ r , i ] * (B ⊕ C) [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (inner r c)⟩
          Σ[ i ← ι n ] ((A [ r , i ] * B [ i , c ]) + (A [ r , i ] * C [ i , c ]))
            ≈⟨ sym (Σ.merge _ _ (ι n)) ⟩
          Σ[ i ← ι n ] A [ r , i ] * B [ i , c ] +
          Σ[ i ← ι n ] A [ r , i ] * C [ i , c ]
            ≡⟨ P.sym $ P.cong₂ _+_ (l∘t r c) (l∘t r c) ⟩
          (A ⊗ B) [ r , c ] + (A ⊗ C) [ r , c ]
            ≡⟨ P.sym (l∘t r c) ⟩
          ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ] ∎

    ⊗-distrOverʳ-⊕ : (_≋_ DistributesOverʳ _⊗_) _⊕_
    ⊗-distrOverʳ-⊕ C A B = ext distr
      where
        open Semiring semiring using (*-cong; distrib)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne

        distr : ∀ r c → ((A ⊕ B) ⊗ C) [ r , c ] ≈ ((A ⊗ C) ⊕ (B ⊗ C)) [ r , c ]
        distr r c = begin
          ((A ⊕ B) ⊗ C) [ r , c ]
            ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] (A ⊕ B) [ r , i ] * C [ i , c ]
            ≈⟨ Σ.cong (ι n) P.refl (λ i → begin

              (A ⊕ B) [ r , i ] * C [ i , c ]
                ≈⟨ *-cong (reflexive (l∘t r i)) refl ⟩
              (A [ r , i ] + B [ r , i ]) * C [ i , c ]
                ≈⟨ proj₂ distrib _ _ _ ⟩
              (A [ r , i ] * C [ i , c ]) + (B [ r , i ] * C [ i , c ]) ∎)⟩

          Σ[ i ← ι n ] ((A [ r , i ] * C [ i , c ]) + (B [ r , i ] * C [ i , c ]))
            ≈⟨ sym (Σ.merge _ _ (ι n)) ⟩
          Σ[ i ← ι n ] A [ r , i ] * C [ i , c ] +
          Σ[ i ← ι n ] B [ r , i ] * C [ i , c ]
            ≡⟨ P.sym $ P.cong₂ _+_ (l∘t r c) (l∘t r c) ⟩
          (A ⊗ C) [ r , c ] + (B ⊗ C) [ r , c ]
            ≡⟨ P.sym (l∘t r c) ⟩
          ((A ⊗ C) ⊕ (B ⊗ C)) [ r , c ] ∎

    ------------------------
    -- It's a … semiring! --
    ------------------------

    M-isSemiring : IsSemiring _≋_ _⊕_ _⊗_ 0M 1M
    M-isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isSemigroup = record
            { isEquivalence = ≋-isEquivalence
            ; assoc         = ⊕-assoc
            ; ∙-cong        = ⊕-cong
            }
          ; identityˡ       = ⊕-identityˡ
          ; comm            = ⊕-comm
          }
        ; *-isMonoid = record
          { isSemigroup = record
            { isEquivalence = ≋-isEquivalence
            ; assoc         = ⊗-assoc
            ; ∙-cong        = ⊗-cong
            }
          ; identity        = ⊗-identityˡ , ⊗-identityʳ
          }
        ; distrib           = ⊗-distrOverˡ-⊕ , ⊗-distrOverʳ-⊕
        }
      ; zero                = M-zeroˡ , M-zeroʳ
      }
