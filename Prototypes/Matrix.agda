module Prototypes.Matrix where

  import Data.Vec as V
  open import Data.Fin using (Fin)
  open import Data.Nat.Base using (ℕ)

  Matrix : ∀ {a} (A : Set a) → ℕ → ℕ → Set a
  Matrix A r c = V.Vec (V.Vec A c) r

  lookup : ∀ {r c a} {A : Set a} → Fin r → Fin c → Matrix A r c → A
  lookup {r} {c} i j m = V.lookup j (V.lookup i m)
