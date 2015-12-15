module Test where
  
  open import Algebra

  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  open P.≡-Reasoning

  open import Data.Nat using (suc)
  open import Data.Nat.Properties using (commutativeSemiring)
  open import Data.Product using (proj₁; proj₂)
  open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

  open import Bigop
  open import Bigop.Interval.Nat
  open Fold +-monoid using (Σ-syntax)
  open Props.Interval.Nat

  proof : ∀ n → 2 * (Σ[ i ← 0 to n ] i) ≡ n * (suc n)
  proof 0 = P.refl
  proof (suc n) =
      begin
        2 * (Σ[ i ← 0 to suc n ] i)          ≡⟨ P.cong (_*_ 2) lemma ⟩
        2 * ((Σ[ i ← 0 to n ] i) + suc n)    ≡⟨ proj₁ distrib 2 (Σ[ i ← 0 to n ] i) (suc n) ⟩
        2 * (Σ[ i ← 0 to n ] i) + 2 * suc n  ≡⟨ P.cong₂ _+_ (proof n) P.refl ⟩
        n * suc n + 2 * suc n                ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
        2 * suc n + n * suc n                ≡⟨ P.sym (proj₂ distrib (suc n) 2 n) ⟩
        (2 + n) * suc n                      ≡⟨ *-comm (2 + n) (suc n) ⟩
        suc n * (suc (suc n))
      ∎
      where
        --- This should be a lemma in Bigop.Interval.Nat
        open import Function
        open import Data.List.Base
        module Σ = Props.SemiringWithoutOne semiringWithoutOne
        open Fold +-monoid using (fold)
        lemma : Σ[ i ← 0 to suc n ] i ≡ (Σ[ i ← 0 to n ] i) + suc n
        lemma =
          begin
            Σ[ i ← 0 to suc n ] i       ≡⟨ P.cong (fold id) (upFrom-last 1 n) ⟩
            Σ[ i ← 0 to n ∷ʳ suc n ] i  ≡⟨ Σ.snoc id (suc n) (0 to n) ⟩
            (Σ[ i ← 0 to n ] i) + suc n
          ∎

                                       

