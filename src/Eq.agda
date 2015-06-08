module Eq where

open import Data.Nat.Base
open import Data.Nat.Properties.Simple

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

equiv₁ : (p q r : ℕ) → (p * q) * r ≡ q * (p * r)
equiv₁ p q r =
  begin
    (p *  q) * r  ≡⟨ cong₂ _*_ (*-comm p q) refl ⟩
    (q *  p) * r  ≡⟨ *-assoc q p r ⟩
    q * (p  * r)
  ∎
