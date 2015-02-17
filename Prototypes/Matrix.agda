module Prototypes.Matrix where

  import Data.Vec as V
  open import Data.Fin using (Fin)
  open import Data.Nat.Base using (ℕ)

  Matrix : ∀ {a} (A : Set a) → ℕ → ℕ → Set a
  Matrix A r c = V.Vec (V.Vec A c) r

  lookup : ∀ {r c a} {A : Set a} → Fin r → Fin c → Matrix A r c → A
  lookup {r} {c} i j m = V.lookup j (V.lookup i m)

  tabulate : ∀ {r c a} {A : Set a} → (Fin r → Fin c → A) → Matrix A r c
  tabulate f = V.tabulate (λ r → V.tabulate (λ c → f r c))

  transpose : ∀ {r c a} {A : Set a} → Matrix A r c → Matrix A c r
  transpose {r} {c} m = tabulate (λ c r → lookup r c m)

  -- TODO: turn this into a syntax declaration
  _[_,_] : ∀ {r c a} {A : Set a} → Matrix A r c → Fin r → Fin c → A
  m [ i , j ] = lookup i j m
