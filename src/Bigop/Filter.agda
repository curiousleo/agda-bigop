module Bigop.Filter where

open import Bigop.Ordinals

open import Data.List.Base using (List; _∷_; [])
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred; Decidable; ∁)

infixl 5 _∥_

_∥_ : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → List I → Decidable P → List I
[]       ∥ dec = []
(i ∷ is) ∥ dec with dec i
(i ∷ is) ∥ dec | yes _ = i ∷ (is ∥ dec)
(i ∷ is) ∥ dec | no  _ =      is ∥ dec

-- equivalent to `filter (⌊_⌋ ∘ dec) is`

∁′ : ∀ {i ℓ} {I : Set i} {P : Pred I ℓ} → Decidable P → Decidable (∁ P)
∁′ p x with p x
∁′ p x | yes q = no (λ ¬q → ¬q q)
∁′ p x | no ¬q = yes (λ q → ¬q q)

open import Function using (_⟨_⟩_)
open import Data.Nat.Base using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
open import Relation.Binary using () renaming (Decidable to BDecidable)
open import Relation.Binary.Core using (_≡_)
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

≟ : {n : ℕ} → BDecidable {A = Fin n} _≡_
≟ {zeroℕ}  ()       ()
≟ {sucℕ n} zeroF    zeroF    = yes P.refl
≟ {sucℕ n} zeroF    (sucF q) = no (λ ())
≟ {sucℕ n} (sucF p) zeroF    = no (λ ())
≟ {sucℕ n} (sucF p) (sucF  q) with ≟ p q
≟ {sucℕ n} (sucF p) (sucF .p) | yes P.refl = yes P.refl
≟ {sucℕ n} (sucF p) (sucF  q) | no ¬eq = no (suc-lemma ¬eq)
  where
    open import Data.Empty
    suc-lemma : {n : ℕ} {p q : Fin n} →
                ¬ p ≡ q → ¬ sucF p ≡ sucF q
    suc-lemma eq P.refl = ⊥-elim (eq P.refl)

private
 module Test where

  open import Bigop.Ordinals
  open import Bigop.Filter.Predicates

  open import Relation.Binary.PropositionalEquality

  test-even : (upFromℕ 1 6) ∥ even ≡ 2 ∷ 4 ∷ 6 ∷ []
  test-even = refl

  test-odd : (upFromℕ 1 6) ∥ odd ≡ 1 ∷ 3 ∷ 5 ∷ []
  test-odd = refl
