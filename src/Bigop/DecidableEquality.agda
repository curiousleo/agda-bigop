module Bigop.DecidableEquality where

open import Data.Empty
open import Data.Fin
open import Data.Nat.Base
open import Relation.Binary using (Decidable)
open import Relation.Binary.Core
open import Relation.Nullary

≟N : Decidable {A = ℕ} _≡_
≟N zero    zero    = yes refl
≟N zero    (suc n) = no (λ ())
≟N (suc m) zero    = no (λ ())
≟N (suc m) (suc n) with ≟N m n
≟N (suc m) (suc .m) | yes refl = yes refl
≟N (suc m) (suc n)  | no ¬eq   = no (suc-lem ¬eq)
  where
    suc-lem : {m n : ℕ} → ¬ m ≡ n → ¬ ℕ.suc m ≡ suc n
    suc-lem ¬eq refl = ⊥-elim (¬eq refl)

≟F : {n : ℕ} → Decidable {A = Fin n} _≡_
≟F {zero}  ()       ()
≟F {suc n} zero    zero    = yes refl
≟F {suc n} zero    (suc q) = no (λ ())
≟F {suc n} (suc p) zero    = no (λ ())
≟F {suc n} (suc p) (suc  q) with ≟F p q
≟F {suc n} (suc p) (suc .p) | yes refl = yes refl
≟F {suc n} (suc p) (suc  q) | no ¬eq = no (suc-lem ¬eq)
  where
    suc-lem : {n : ℕ} {p q : Fin n} →
              ¬ p ≡ q → ¬ Fin.suc p ≡ suc q
    suc-lem ¬eq refl = ⊥-elim (¬eq refl)
