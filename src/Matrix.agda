module Matrix where

open import Data.Fin using (Fin)
open import Data.Nat.Base using (ℕ)
import Data.Vec as V
open V using (Vec)
import Data.Vec.Properties as VP
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)
open P.≡-Reasoning

------------------------------------------------------------------------
-- The type of r × c matrices over carrier type A

Matrix : ∀ {a} (A : Set a) → ℕ → ℕ → Set a
Matrix A r c = Vec (Vec A c) r

------------------------------------------------------------------------
-- Looking up values in a matrix

lookup : ∀ {r c a} {A : Set a} → Fin r → Fin c → Matrix A r c → A
lookup i j m = V.lookup j (V.lookup i m)

_[_,_] : ∀ {r c a} {A : Set a} → Matrix A r c → Fin r → Fin c → A
m [ i , j ] = lookup i j m

------------------------------------------------------------------------
-- Creating and manipulating matrices

tabulate : ∀ {r c a} {A : Set a} → (Fin r → Fin c → A) → Matrix A r c
tabulate f = V.tabulate (λ r → V.tabulate (λ c → f r c))

transpose : ∀ {r c a} {A : Set a} → Matrix A r c → Matrix A c r
transpose m = tabulate (λ c r → lookup r c m)

------------------------------------------------------------------------
-- Tabulate is an inverse of (flip lookup)

lookup∘tabulate : ∀ {a n} {A : Set a} {f : Fin n → Fin n → A} r c →
                  lookup r c (tabulate f) ≡ f r c
lookup∘tabulate {f = f} r c = begin
  V.lookup c (V.lookup r (V.tabulate (V.tabulate ∘ f)))
    ≡⟨ P.cong (V.lookup c) (VP.lookup∘tabulate (V.tabulate ∘ f) r) ⟩
  V.lookup c (V.tabulate (f r))
    ≡⟨ VP.lookup∘tabulate (f r) c ⟩
  f r c ∎
