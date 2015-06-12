module Data.Nat.Combinatorics.Combinatorics where

open import Algebra

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Product

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_)
open import Relation.Binary.SetoidReasoning

--
-- Binomial coefficients
--

_choose_ : ℕ → ℕ → ℕ
_     choose 0     = 1
0     choose suc k = 0
suc n choose suc k = n choose k + n choose (suc k)

--
-- Factorial
--

_! : ℕ → ℕ
0 !     = 1
suc n ! = suc n Nat.* (n !)

-- XXX: rewrite choose-greedy in terms of this…
choose-+ : ∀ m n → n choose ((suc m) + n) ≡ 0
choose-+ m zero    = P.refl
choose-+ m (suc n) =
  begin⟨ P.setoid ℕ ⟩
    suc n choose (suc m + suc n)
      ≡⟨ P.cong (_choose_ (suc n)) (+-suc (suc m) n) ⟩
    suc n choose (suc (suc (m + n)))
      ≡⟨ P.refl ⟩
    (n choose suc (m + n)) + (n choose (suc (suc (m + n))))
      ≡⟨ +-cong (choose-+ m n) (choose-+ (suc m) n) ⟩
    0 + 0
      ≡⟨ P.refl ⟩
    0
  ∎
  where
    choose-cong : ∀ m → ∀ {o p} → o ≡ p → m choose o ≡ m choose p
    choose-cong m P.refl = P.refl

    +-cong : ∀ {m₁ m₂ n₁ n₂} → m₁ ≡ m₂ → n₁ ≡ n₂ → m₁ + n₁ ≡ m₂ + n₂
    +-cong P.refl P.refl = P.refl

choose-greedy : ∀ m n → n < m → n choose m ≡ 0
choose-greedy zero    n       ()
choose-greedy (suc m) zero    n<m       = P.refl
choose-greedy (suc m) (suc n) (s≤s n<m) =
  begin⟨ P.setoid ℕ ⟩
    n choose m + n choose suc m
      ≡⟨ P.cong (λ x → x + n choose suc m) (choose-greedy m n n<m) ⟩
    0 + n choose suc m
      ≡⟨ P.cong (_+_ 0) (choose-greedy (suc m) n (≤-step n<m)) ⟩
    0 + 0
      ≡⟨ P.refl ⟩
    0
  ∎

choose-exact : ∀ n → n choose n ≡ 1
choose-exact zero    = P.refl
choose-exact (suc n) =
  begin⟨ P.setoid ℕ ⟩
    n choose n + n choose suc n
      ≡⟨ P.cong (λ x → x + n choose suc n) (choose-exact n) ⟩
    1 + n choose suc n
      ≡⟨ P.cong suc (choose-greedy (suc n) n refl) ⟩
    1 + 0
      ≡⟨ +-right-identity 1 ⟩
    1
  ∎
  where open DecTotalOrder decTotalOrder

pascal's-identity : ∀ m n → suc m choose suc n ≡ m choose n + m choose suc n
pascal's-identity zero    zero    = P.refl
pascal's-identity zero    (suc n) = P.refl
pascal's-identity (suc m) zero    = P.refl
pascal's-identity (suc m) (suc n) = P.refl

--
-- The nth Fibonacci number
--

fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

--
-- Powers in an arbitrary monoid
--

module RequiresMonoid {c} {ℓ} (mon : Monoid c ℓ) where

  open Monoid mon

  infixr 8 _^_

  _^_ : Carrier → ℕ → Carrier
  b ^ zero  = ε
  b ^ suc p = b ∙ b ^ p

  pow-one : ∀ b → b ^ 1 ≈ b
  pow-one b = proj₂ identity b

  one-pow : ∀ m → ε ^ m ≈ ε
  one-pow zero    = refl
  one-pow (suc m) =
    begin⟨ setoid ⟩
      ε ^ (suc m)
        ≡⟨ P.refl ⟩
      ε ∙ ε ^ m
        ≈⟨ proj₁ identity (ε ^ m) ⟩
      ε ^ m
        ≈⟨ one-pow m ⟩
      ε
    ∎

  pow-+ : ∀ b m n → b ^ (m + n) ≈ b ^ m ∙ b ^ n
  pow-+ b zero    n = sym $ proj₁ identity $ b ^ n
  pow-+ b (suc m) n =
    begin⟨ setoid ⟩
      b ∙ b ^ (m + n)
        ≈⟨ ∙-cong refl $ pow-+ b m n ⟩
      b ∙ (b ^ m ∙ b ^ n)
        ≈⟨ sym $ assoc b (b ^ m) (b ^ n) ⟩
      (b ∙ b ^ m) ∙ b ^ n
        ≈⟨ refl ⟩
      b ^ (suc m) ∙ b ^ n
    ∎

module RequiresCommutativeMonoid {c} {ℓ} (com : CommutativeMonoid c ℓ) where

  open CommutativeMonoid com
  open RequiresMonoid monoid

  pow-∙ : ∀ b c m → (b ∙ c) ^ m ≈ b ^ m ∙ c ^ m
  pow-∙ b c zero    = sym $ proj₂ identity ε
  pow-∙ b c (suc m) =
    begin⟨ setoid ⟩
      (b ∙ c) ^ suc m
        ≡⟨ P.refl ⟩
      (b ∙ c) ∙ (b ∙ c) ^ m
        ≈⟨ ∙-cong refl $ pow-∙ b c m ⟩
      (b ∙ c) ∙ (b ^ m ∙ c ^ m)
        ≈⟨ ∙-cong (comm b c) refl ⟩
      (c ∙ b) ∙ (b ^ m ∙ c ^ m)
        ≈⟨ assoc c b $ (b ^ m) ∙ (c ^ m) ⟩
      c ∙ (b ∙ (b ^ m ∙ c ^ m))
        ≈⟨ ∙-cong refl $ sym $ assoc b (b ^ m) (c ^ m) ⟩
      c ∙ (b ∙ b ^ m ∙ c ^ m)
        ≡⟨ P.refl ⟩
      c ∙ (b ^ suc m ∙ c ^ m)
        ≈⟨ ∙-cong refl $ comm (b ^ suc m) (c ^ m) ⟩
      c ∙ (c ^ m ∙ b ^ suc m)
        ≈⟨ sym $ assoc c (c ^ m) (b ^ suc m) ⟩
      (c ∙ c ^ m) ∙ b ^ suc m
        ≡⟨ P.refl ⟩
      c ^ suc m ∙ b ^ suc m
        ≈⟨ comm (c ^ suc m) (b ^ suc m) ⟩
      b ^ suc m ∙ c ^ suc m
    ∎
