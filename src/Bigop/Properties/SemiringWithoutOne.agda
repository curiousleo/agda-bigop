------------------------------------------------------------------------
-- Big operator library
--
-- Equivalences for big operators over a "semiring without one"
------------------------------------------------------------------------

open import Algebra

module Bigop.Properties.SemiringWithoutOne
       {c ℓ} (S : SemiringWithoutOne c ℓ) where

open import Bigop.Core
import Bigop.Properties.CommutativeMonoid as CommutativeMonoidProps

open import Data.List.Base
open import Data.Product hiding (map)
open import Function

open SemiringWithoutOne S
open CommutativeMonoidProps
open RequiresCommutativeMonoid {c} {ℓ} +-commutativeMonoid public

open import Relation.Binary.EqReasoning setoid
open Fold +-monoid

-- Left-distributivity for big operators

distrˡ : ∀ {i} {I : Set i} (f : I → Carrier) (x : Carrier) (is : List I) →
           x * fold f is ≈ fold (λ k → x * (f k)) is
distrˡ f x [] = proj₂ zero x
distrˡ f x (n ∷ ns) = begin
  x * (f n + fold f ns)
    ≈⟨ proj₁ distrib x (f n) (fold f ns) ⟩
  (x * f n) + (x * fold f ns)
    ≈⟨ refl {x * f n} ⟨ +-cong ⟩ distrˡ f x ns ⟩
  (x * f n) + fold ((_*_ x) ∘ f) ns ∎

-- Right-distributivity for big operators

distrʳ : ∀ {i} {I : Set i} (f : I → Carrier) (x : Carrier) (is : List I) →
           fold f is * x ≈ fold (λ k → (f k) * x) is
distrʳ f x [] = proj₁ zero x
distrʳ f x (n ∷ ns) = begin
  (f n + fold f ns) * x
     ≈⟨ proj₂ distrib x (f n) (fold f ns) ⟩
  (f n * x) + (fold f ns * x)
     ≈⟨ refl {f n * x} ⟨ +-cong ⟩ distrʳ f x ns ⟩
  (f n * x) + fold (λ k → (f k) * x) ns ∎
