open import Algebra

module Bigop.Properties.SemiringWithoutOne
       {c ℓ} (S : SemiringWithoutOne c ℓ) where

open import Bigop.Core
-- open import Bigop.Filter
import Bigop.Properties.CommutativeMonoid as CommutativeMonoidProps

open import Data.List.Base
open import Data.Product hiding (map)
open import Function

open SemiringWithoutOne S renaming (Carrier to R; zero to *-zero)
open CommutativeMonoidProps {c} {ℓ} +-commutativeMonoid public

open import Relation.Binary.EqReasoning setoid
open Fold +-monoid

Σ-distrˡ : ∀ {i} {I : Set i} (f : I → R) (x : R) (is : List I) →
           x * fold f is ≈ fold (λ k → x * (f k)) is
Σ-distrˡ f x [] = proj₂ *-zero x
Σ-distrˡ f x (n ∷ ns) = begin
  x * (f n + fold f ns)
    ≈⟨ proj₁ distrib x (f n) (fold f ns) ⟩
  (x * f n) + (x * fold f ns)
    ≈⟨ refl {x * f n} ⟨ +-cong ⟩ Σ-distrˡ f x ns ⟩
  (x * f n) + fold ((_*_ x) ∘ f) ns ∎

Σ-distrʳ : ∀ {i} {I : Set i} (f : I → R) (x : R) (is : List I) →
           fold f is * x ≈ fold (λ k → (f k) * x) is
Σ-distrʳ f x [] = proj₁ *-zero x
Σ-distrʳ f x (n ∷ ns) = begin
  (f n + fold f ns) * x
     ≈⟨ proj₂ distrib x (f n) (fold f ns) ⟩
  (f n * x) + (fold f ns * x)
     ≈⟨ refl {f n * x} ⟨ +-cong ⟩ Σ-distrʳ f x ns ⟩
  (f n * x) + fold (λ k → (f k) * x) ns ∎