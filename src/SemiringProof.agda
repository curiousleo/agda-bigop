open import Algebra
open import Data.Nat.Base using (ℕ; z≤n)

module SemiringProof (n : ℕ) {c ℓ} (semiring : Semiring c ℓ) where

open import Bigop
open import Bigop.DecidableEquality using () renaming (≟F to ≟)
open import Matrix

open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Empty
open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
open import Data.Fin.Properties using (bounded)
import Data.List.Base as L using ([_])
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

open Semiring semiring
  using (Carrier;
         0#; 1#; _+_; _*_;
         setoid;
         +-semigroup; +-monoid; +-commutativeMonoid;
         *-semigroup; *-monoid;
         semiringWithoutOne)

open Setoid setoid using (_≈_; refl; sym; trans; reflexive; isEquivalence)

open Fold +-monoid using (Σ-syntax)
open Props.Interval.Fin
open import Bigop.Interval.Fin

open import Relation.Binary.EqReasoning setoid
open P.≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)

-----------------
-- Definitions --
-----------------

M : Set c
M = Matrix Carrier n n

infix 4 _≋_

_≋_ : Rel M ℓ
_≋_ = Pointwise _≈_

_⊕_ : Op₂ M
A ⊕ B = tabulate (λ r c → A [ r , c ] + B [ r , c ])

mult : M → M → Fin n → Fin n → Carrier
mult A B r c = Σ[ i ← 0 …< n ] A [ r , i ] * B [ i , c ]

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

1M-diag : ∀ {r c} → r ≡ c → 1M [ r , c ] ≡ 1#
1M-diag {r} {.r} P.refl = start
  1M [ r , r ]  ≣⟨ lookup∘tabulate r r ⟩
  diag r r      ≣⟨ diag-lemma r ⟩
  1#            □
    where

    diag-lemma : ∀ {n} (r : Fin n) → diag r r ≡ 1#
    diag-lemma zeroF    = P.refl
    diag-lemma (sucF r) = diag-lemma r

1M-∁-diag : ∀ {r c} → ∁ (_≡_ r) c → 1M [ r , c ] ≡ 0#
1M-∁-diag {r} {c}  eq with ≟ r c
1M-∁-diag {r} {c} ¬eq | yes eq = ⊥-elim (¬eq eq)
1M-∁-diag {r} {c} ¬eq | no  _  = start
  1M [ r , c ]  ≣⟨ lookup∘tabulate r c ⟩
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

⊕-assoc : Associative _≋_ _⊕_
⊕-assoc A B C = assoc
  where
    open Semigroup +-semigroup using () renaming (assoc to +-assoc)

    factorₗ : ∀ r c →
              ((A ⊕ B) ⊕ C) [ r , c ] ≡ (A [ r , c ] + B [ r , c ]) + C [ r , c ]
    factorₗ r c = start
      ((A ⊕ B) ⊕ C) [ r , c ]          ≣⟨ lookup∘tabulate r c ⟩
      (A ⊕ B) [ r , c ] + C [ r , c ]  ≣⟨ P.cong₂ _+_ (lookup∘tabulate r c) P.refl ⟩
      (A [ r , c ] + B [ r , c ]) + C [ r , c ] □

    factorᵣ : ∀ r c →
              (A ⊕ (B ⊕ C)) [ r , c ] ≡ A [ r , c ] + (B [ r , c ] + C [ r , c ])
    factorᵣ r c = start
      (A ⊕ (B ⊕ C)) [ r , c ]          ≣⟨ lookup∘tabulate r c ⟩
      A [ r , c ] + (B ⊕ C) [ r , c ]  ≣⟨ P.cong₂ _+_ P.refl (lookup∘tabulate r c) ⟩
      A [ r , c ] + (B [ r , c ] + C [ r , c ]) □

    assoc : ∀ r c → ((A ⊕ B) ⊕ C) [ r , c ] ≈ (A ⊕ (B ⊕ C)) [ r , c ]
    assoc r c = begin
      ((A ⊕ B) ⊕ C) [ r , c ]                      ≡⟨ factorₗ r c ⟩
      (A [ r , c ] +  B [ r , c ]) + C [ r , c ]   ≈⟨ +-assoc _ _ _ ⟩
       A [ r , c ] + (B [ r , c ]  + C [ r , c ])  ≡⟨ P.sym (factorᵣ r c) ⟩
      (A ⊕ (B ⊕ C)) [ r , c ]                      ∎

⊕-cong : _⊕_ Preserves₂ _≋_ ⟶ _≋_ ⟶ _≋_
⊕-cong {A} {A′} {B} {B′} eq₁ eq₂ = cong
  where
    open Semigroup +-semigroup using () renaming (∙-cong to +-cong)

    cong : ∀ r c → (A ⊕ B) [ r , c ] ≈ (A′ ⊕ B′) [ r , c ]
    cong r c = begin
      (A ⊕ B) [ r , c ]            ≡⟨ lookup∘tabulate r c ⟩
      A [ r , c ] + B [ r , c ]    ≈⟨ +-cong (eq₁ r c) (eq₂ r c) ⟩
      A′ [ r , c ] + B′ [ r , c ]  ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      (A′ ⊕ B′) [ r , c ]          ∎

⊕-identityˡ : LeftIdentity _≋_ 0M _⊕_
⊕-identityˡ A = ident
  where
    open Monoid +-monoid using () renaming (identity to +-identity)

    ident : ∀ r c → (0M ⊕ A) [ r , c ] ≈ A [ r , c ]
    ident r c = begin
      (0M ⊕ A) [ r , c ]          ≡⟨ lookup∘tabulate r c ⟩
      0M [ r , c ] + A [ r , c ]  ≡⟨ P.cong₂ _+_ (lookup∘tabulate r c) P.refl ⟩
                0# + A [ r , c ]  ≈⟨ proj₁ +-identity _ ⟩
                     A [ r , c ]  ∎

⊕-comm : Commutative _≋_ _⊕_
⊕-comm A B = comm
  where
    open CommutativeMonoid +-commutativeMonoid using () renaming (comm to +-comm)

    comm : ∀ r c → (A ⊕ B) [ r , c ] ≈ (B ⊕ A) [ r , c ]
    comm r c = begin
      (A ⊕ B) [ r , c ]          ≡⟨ lookup∘tabulate r c ⟩
      A [ r , c ] + B [ r , c ]  ≈⟨ +-comm _ _ ⟩
      B [ r , c ] + A [ r , c ]  ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      (B ⊕ A) [ r , c ] ∎

M-zeroˡ : LeftZero _≋_ 0M _⊗_
M-zeroˡ A = z
  where
    open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
    module Σ = Props.Monoid +-monoid using (cong; identity)

    z : ∀ r c → (0M ⊗ A) [ r , c ] ≈ 0M [ r , c ]
    z r c = begin
      (0M ⊗ A) [ r , c ]               ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] 0M [ r , i ] * A [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl
                  (λ i → reflexive (lookup∘tabulate r i) ⟨ *-cong ⟩ refl) ⟩
      Σ[ i ← 0 …< n ] 0# * A [ i , c ]  ≈⟨ Σ.cong (0 …< n) P.refl (λ i → proj₁ zero _) ⟩
      Σ[ i ← 0 …< n ] 0#                ≈⟨ Σ.identity (0 …< n) ⟩
      0#                               ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      0M [ r , c ]                     ∎

M-zeroʳ : RightZero _≋_ 0M _⊗_
M-zeroʳ A = z
  where
    open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne

    z : ∀ r c → (A ⊗ 0M) [ r , c ] ≈ 0M [ r , c ]
    z r c = begin
      (A ⊗ 0M) [ r , c ]                 ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * 0M [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl
                  (λ i → *-cong refl (reflexive (lookup∘tabulate i c))) ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * 0#    ≈⟨ sym (Σ.distrʳ _ 0# (0 …< n)) ⟩
      (Σ[ i ← 0 …< n ] A [ r , i ]) * 0#  ≈⟨ proj₂ zero _ ⟩
      0#                                 ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      0M [ r , c ]                       ∎

⊗-assoc : Associative _≋_ _⊗_
⊗-assoc A B C = assoc
  where
    open SemiringWithoutOne semiringWithoutOne using (*-assoc; *-cong)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne

    factorˡ : ∀ r c →
              ((A ⊗ B) ⊗ C) [ r , c ] ≈
              Σ[ i ← 0 …< n ] (Σ[ j ← 0 …< n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
    factorˡ r c = begin
      ((A ⊗ B) ⊗ C) [ r , c ]
        ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] (A ⊗ B) [ r , i ] * C [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (λ i → *-cong (reflexive (lookup∘tabulate r i)) refl) ⟩
      Σ[ i ← 0 …< n ] (Σ[ j ← 0 …< n ] A [ r , j ] * B [ j , i ]) * C [ i , c ] ∎

    factorʳ : ∀ r c →
              (A ⊗ (B ⊗ C)) [ r , c ] ≈
              Σ[ j ← 0 …< n ] A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
    factorʳ r c = begin
      (A ⊗ (B ⊗ C)) [ r , c ]
        ≡⟨ lookup∘tabulate r c ⟩
      Σ[ j ← 0 …< n ] A [ r , j ] * (B ⊗ C) [ j , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (λ j → *-cong refl (reflexive (lookup∘tabulate j c))) ⟩
      Σ[ j ← 0 …< n ] A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ]) ∎

    inner : ∀ r c j →
            Σ[ i ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ] ≈
            A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
    inner r c j = begin
      Σ[ i ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (λ i → *-assoc _ _ _) ⟩
      Σ[ i ← 0 …< n ] A [ r , j ] * (B [ j , i ] * C [ i , c ])
        ≈⟨ sym (Σ.distrˡ _ _ (0 …< n)) ⟩
      A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ]) ∎

    assoc : ∀ r c → ((A ⊗ B) ⊗ C) [ r , c ] ≈ (A ⊗ (B ⊗ C)) [ r , c ]
    assoc r c = begin
      ((A ⊗ B) ⊗ C) [ r , c ]
        ≈⟨ factorˡ r c ⟩
      Σ[ i ← 0 …< n ] (Σ[ j ← 0 …< n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (λ i → Σ.distrʳ _ _ (0 …< n)) ⟩
      Σ[ i ← 0 …< n ] Σ[ j ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
        ≈⟨ Σ.swap _ (0 …< n) (0 …< n) ⟩
      Σ[ j ← 0 …< n ] Σ[ i ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (inner r c) ⟩
      Σ[ j ← 0 …< n ] A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
        ≈⟨ sym $ factorʳ r c ⟩
      (A ⊗ (B ⊗ C)) [ r , c ] ∎

⊗-cong : _⊗_ Preserves₂ _≋_ ⟶ _≋_ ⟶ _≋_
⊗-cong {u} {v} {A} {B} eq₁ eq₂ = cong
  where
    open Semigroup *-semigroup using () renaming (∙-cong to *-cong)
    module Σ = Props.Monoid +-monoid

    cong : ∀ r c → (u ⊗ A) [ r , c ] ≈ (v ⊗ B) [ r , c ]
    cong r c = begin
      (u ⊗ A) [ r , c ]
        ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] u [ r , i ] * A [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (λ i → *-cong (eq₁ r i) (eq₂ i c)) ⟩
      Σ[ i ← 0 …< n ] v [ r , i ] * B [ i , c ]
        ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      (v ⊗ B) [ r , c ] ∎

⊗-identityˡ : LeftIdentity _≋_ 1M _⊗_
⊗-identityˡ A = ident
  where
    open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne
      using (cong-P; split-P; distrˡ)

    ≡-step : ∀ r c →  Σ[ i ← 0 …< n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ] ≈
                      Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ]
    ≡-step r c = begin
      Σ[ i ← 0 …< n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ]
        ≈⟨ Σ.cong-P  (0 …< n) (≟ r)
                     (λ i r≡i → reflexive (1M-diag r≡i) ⟨ *-cong ⟩ refl) ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ] 1# * A [ i , c ]    ≈⟨ sym $ Σ.distrˡ _ 1# (0 …< n ∥ ≟ r) ⟩
      1# * (Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ])  ≈⟨ proj₁ *-identity _ ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ]         ∎

    ≢-step : ∀ r c → Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ] ≈ 0#
    ≢-step r c = begin
      Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ]
        ≈⟨ Σ.cong-P  (0 …< n) (∁′ (≟ r))
                     (λ i r≢i → reflexive (1M-∁-diag r≢i) ⟨ *-cong ⟩ refl) ⟩
      Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ] 0# * A [ i , c ]      ≈⟨ sym $ Σ.distrˡ _ 0# (0 …< n ∥ ∁′ (≟ r)) ⟩
      0# * (Σ[ i ← 0 …< n ∥ (∁′ (≟ r)) ] A [ i , c ])  ≈⟨ proj₁ zero _ ⟩
      0#                                              ∎

    filter : ∀ r c → 0 …< n ∥ ≟ r ≡ L.[ r ]
    filter r c = ordinals-filter z≤n (bounded r)

    ident : ∀ r c → (1M ⊗ A) [ r , c ] ≈ A [ r , c ]
    ident r c = begin
      (1M ⊗ A) [ r , c ]                                      ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] 1M [ r , i ] * A [ i , c ]               ≈⟨ Σ.split-P _ (0 …< n) (≟ r) ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ]       1M [ r , i ] * A [ i , c ] +
      Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ]  1M [ r , i ] * A [ i , c ]    ≈⟨ ≡-step r c ⟨ +-cong ⟩ ≢-step r c ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ] + 0#                    ≈⟨ proj₂ +-identity _ ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ]                         ≡⟨ P.cong  (Σ-syntax (λ i → A [ i , c ]))
                                                                        (filter r c) ⟩
      A [ r , c ] + 0#                                        ≈⟨ proj₂ +-identity _  ⟩
      A [ r , c ]                                             ∎

⊗-identityʳ : RightIdentity _≋_ 1M _⊗_
⊗-identityʳ A = ident
  where
    open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne

    ∁-sym : ∀ {a} {A : Set a} {A B : A} → ∁ (_≡_ A) B → ∁ (λ C → B ≡ C) A
    ∁-sym eq P.refl = eq P.refl

    ident : ∀ r c → (A ⊗ 1M) [ r , c ] ≈ A [ r , c ]
    ident r c = begin
      (A ⊗ 1M) [ r , c ]
        ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * 1M [ i , c ]
        ≈⟨ Σ.split-P _ (0 …< n) (≟ c) ⟩
      Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ] * 1M [ i , c ] +
      Σ[ i ← 0 …< n ∥ ∁′ (≟ c) ] A [ r , i ] * 1M [ i , c ]
        ≈⟨ +-cong
             (Σ.cong-P (0 …< n) (≟ c)
                       (λ i c≡i → *-cong refl
                                         (reflexive (1M-diag (P.sym c≡i)))))
             (Σ.cong-P (0 …< n) (∁′ (≟ c))
                       (λ i c≢i → *-cong refl
                                         (reflexive (1M-∁-diag (∁-sym c≢i))))) ⟩
      Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ] * 1# +
      Σ[ i ← 0 …< n ∥ ∁′ (≟ c) ] A [ r , i ] * 0#
        ≈⟨ sym $ +-cong (Σ.distrʳ _ 1# (0 …< n ∥ (≟ c)))
                        (Σ.distrʳ _ 0# (0 …< n ∥ ∁′ (≟ c))) ⟩
      (Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ]) * 1# +
      (Σ[ i ← 0 …< n ∥ (∁′ (≟ c)) ] A [ r , i ]) * 0#
        ≈⟨ +-cong (proj₂ *-identity _) (proj₂ zero _) ⟩
      (Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ]) + 0#
        ≈⟨ proj₂ +-identity _ ⟩
      Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ]
        ≡⟨ P.cong (Σ-syntax (λ i → A [ r , i ]))
                  (ordinals-filter z≤n (bounded c)) ⟩
      Σ[ i ← L.[ c ] ] A [ r , i ]
        ≈⟨ proj₂ +-identity _  ⟩
      A [ r , c ] ∎

⊗-distrOverˡ-⊕ : (_≋_ DistributesOverˡ _⊗_) _⊕_
⊗-distrOverˡ-⊕ A B C = distr
  where
    open Semiring semiring using (*-cong; distrib)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne

    inner : ∀ r c i → A [ r , i ] * (B ⊕ C) [ i , c ] ≈
                      A [ r , i ] * B [ i , c ] + A [ r , i ] * C [ i , c ]
    inner r c i = begin
      A [ r , i ] * (B ⊕ C) [ i , c ]
        ≈⟨ *-cong refl (reflexive (lookup∘tabulate i c)) ⟩
      A [ r , i ] * (B [ i , c ] + C [ i , c ])
        ≈⟨ proj₁ distrib _ _ _ ⟩
      (A [ r , i ] * B [ i , c ]) + (A [ r , i ] * C [ i , c ]) ∎

    distr : ∀ r c → (A ⊗ (B ⊕ C)) [ r , c ] ≈ ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ]
    distr r c = begin
      (A ⊗ (B ⊕ C)) [ r , c ]
        ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * (B ⊕ C) [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (inner r c)⟩
      Σ[ i ← 0 …< n ] ((A [ r , i ] * B [ i , c ]) + (A [ r , i ] * C [ i , c ]))
        ≈⟨ sym (Σ.merge _ _ (0 …< n)) ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * B [ i , c ] +
      Σ[ i ← 0 …< n ] A [ r , i ] * C [ i , c ]
        ≡⟨ P.sym $ P.cong₂ _+_ (lookup∘tabulate r c) (lookup∘tabulate r c) ⟩
      (A ⊗ B) [ r , c ] + (A ⊗ C) [ r , c ]
        ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ] ∎

⊗-distrOverʳ-⊕ : (_≋_ DistributesOverʳ _⊗_) _⊕_
⊗-distrOverʳ-⊕ C A B = distr
  where
    open Semiring semiring using (*-cong; distrib)
    module Σ = Props.SemiringWithoutOne semiringWithoutOne

    distr : ∀ r c → ((A ⊕ B) ⊗ C) [ r , c ] ≈ ((A ⊗ C) ⊕ (B ⊗ C)) [ r , c ]
    distr r c = begin
      ((A ⊕ B) ⊗ C) [ r , c ]
        ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] (A ⊕ B) [ r , i ] * C [ i , c ]
        ≈⟨ Σ.cong (0 …< n) P.refl (λ i → begin

          (A ⊕ B) [ r , i ] * C [ i , c ]
            ≈⟨ *-cong (reflexive (lookup∘tabulate r i)) refl ⟩
          (A [ r , i ] + B [ r , i ]) * C [ i , c ]
            ≈⟨ proj₂ distrib _ _ _ ⟩
          (A [ r , i ] * C [ i , c ]) + (B [ r , i ] * C [ i , c ]) ∎)⟩

      Σ[ i ← 0 …< n ] ((A [ r , i ] * C [ i , c ]) + (B [ r , i ] * C [ i , c ]))
        ≈⟨ sym (Σ.merge _ _ (0 …< n)) ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * C [ i , c ] +
      Σ[ i ← 0 …< n ] B [ r , i ] * C [ i , c ]
        ≡⟨ P.sym $ P.cong₂ _+_ (lookup∘tabulate r c) (lookup∘tabulate r c) ⟩
      (A ⊗ C) [ r , c ] + (B ⊗ C) [ r , c ]
        ≡⟨ P.sym (lookup∘tabulate r c) ⟩
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
  where
    ≋-isEquivalence : IsEquivalence _≋_
    ≋-isEquivalence = PW-isEquivalence isEquivalence
