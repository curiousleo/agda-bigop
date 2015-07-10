module Data.Fin.Subset.Extra where

open import Data.Fin hiding (_≤_)
open import Data.Fin.Subset
open import Data.List.Base as L hiding (length)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec as V hiding (toList)

open import Function using (_$_)

open import Relation.Binary.PropositionalEquality

size : {n : ℕ} → Subset n → ℕ
size []             = 0
size (inside  ∷ xs) = suc $ size xs
size (outside ∷ xs) =       size xs

toVec : {n : ℕ} → (sub : Subset n) → Vec (Fin n) (size sub)
toVec []              = []
toVec (inside  ∷ sub) = zero ∷ V.map inject₁ (toVec sub)
toVec (outside ∷ sub) =        V.map inject₁ (toVec sub)

toList : {n : ℕ} → Subset n → List (Fin n)
toList []              = []
toList (inside  ∷ sub) = zero ∷ L.map inject₁ (toList sub)
toList (outside ∷ sub) =        L.map inject₁ (toList sub)

private
  length : ∀ {a} {A : Set a} {n} → Vec A n → ℕ
  length {n = n} _ = n

size-lemma : {n : ℕ} (sub : Subset n) → size sub ≡ length (toVec sub)
size-lemma []              = refl
size-lemma (inside  ∷ sub) = cong suc (size-lemma sub)
size-lemma (outside ∷ sub) = size-lemma sub

size⁅i⁆≡1 : ∀ {n} (i : Fin n) → size ⁅ i ⁆ ≡ 1
size⁅i⁆≡1 {suc n} zero = cong suc (size⊥≡0 {n})
  where
    size⊥≡0 : ∀ {n} → size {n} ⊥ ≡ 0
    size⊥≡0 {zero}  = refl
    size⊥≡0 {suc n} = size⊥≡0 {n}
size⁅i⁆≡1 (suc i) = size⁅i⁆≡1 i

size≤n : {n : ℕ} → (sub : Subset n) → size sub ≤ n
size≤n V.[] = z≤n
size≤n (inside V.∷ sub) = s≤s (size≤n sub)
size≤n (outside V.∷ sub) = ≤-step (size≤n sub)

∁-size : {n : ℕ} → (sub : Subset n) → size (∁ sub) ≡ n ∸ size sub
∁-size V.[]                      = refl
∁-size {suc n} (inside  V.∷ sub) = ∁-size sub
∁-size {suc n} (outside V.∷ sub) = trans (cong suc (∁-size sub)) (sym (+-∸-assoc 1 {n} {size sub} (size≤n sub)))
