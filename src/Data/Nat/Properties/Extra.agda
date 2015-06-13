module Data.Nat.Properties.Extra where

open import Data.Nat.Base
open import Data.Nat.Properties.Simple

open import Relation.Binary.PropositionalEquality

∸‿+‿lemma : ∀ {m n} → m ≤ n → (n ∸ m) + m ≡ n
∸‿+‿lemma {zero}  {n}      m≤n = +-right-identity n
∸‿+‿lemma {suc m} {zero}   ()
∸‿+‿lemma {suc m} {suc n} (s≤s m≤n)
  rewrite +-suc (n ∸ m) m = cong suc (∸‿+‿lemma m≤n)
