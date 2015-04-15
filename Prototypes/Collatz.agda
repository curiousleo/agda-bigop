module Collatz where

open import Data.Empty
open import Data.Fin
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Product using (∃)
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

C : ℕ → Set {- Pred ℕ _ -}
C n = ∃ λ m → iter f (suc n) m ≡ 1
  where
    f : ℕ → ℕ
    f n with n mod 2
    f n | zero     = n div 2
    f n | suc zero = suc (3 * n)
    f n | suc (suc ())

    iter : ∀ {A} → (A → A) → A → ℕ → A
    iter f x zero    = x
    iter f x (suc n) = iter f (f x) n

module _ where
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  test0 : C 0
  test0 = 0 , refl

  test1 : C 1
  test1 = 1 , refl

  test2 : C 2
  test2 = 7 , refl
