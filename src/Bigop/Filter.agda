module Bigop.Filter where

open import Bigop.Ordinals

import Level

open import Data.List.Base using (List; filter)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Unary using (Pred; Decidable; ∁)

infix 5 _∥_

_∥_ : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → List I → Decidable P → List I
is ∥ dec = filter (⌊_⌋ ∘ dec) is

∁-dec : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → Decidable P → Decidable (∁ P)
∁-dec p x with p x
∁-dec p x | yes q = no (λ ¬q → ¬q q)
∁-dec p x | no ¬q = yes (λ q → ¬q q)

open import Data.Nat.Base using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
open import Relation.Binary using () renaming (Decidable to BDecidable)
open import Relation.Binary.Core using (_≡_)
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

_≟F_ : {n : ℕ} → BDecidable {A = Fin n} _≡_
_≟F_ {zeroℕ}  ()       ()
_≟F_ {sucℕ n} zeroF    zeroF    = yes P.refl
_≟F_ {sucℕ n} zeroF    (sucF q) = no (λ ())
_≟F_ {sucℕ n} (sucF p) zeroF    = no (λ ())
_≟F_ {sucℕ n} (sucF p) (sucF  q) with p ≟F q
_≟F_ {sucℕ n} (sucF p) (sucF .p) | yes P.refl = yes P.refl
_≟F_ {sucℕ n} (sucF p) (sucF  q) | no ¬eq = no (suc-lemma ¬eq)
  where
    open import Data.Empty
    suc-lemma : {n : ℕ} {p q : Fin n} →
                ¬ p ≡ q → ¬ sucF p ≡ sucF q
    suc-lemma eq P.refl = ⊥-elim (eq P.refl)

private
 module Test where

  open import Bigop.Ordinals
  open import Bigop.Filter.Predicates

  open import Data.List.Base
  open import Relation.Binary.PropositionalEquality

  test-even : (1 … 6) ∥ even ≡ 2 ∷ 4 ∷ 6 ∷ []
  test-even = refl

  test-odd : (1 … 6) ∥ odd ≡ 1 ∷ 3 ∷ 5 ∷ []
  test-odd = refl
