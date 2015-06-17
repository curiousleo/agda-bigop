open import Dijkstra.Algebra

module Dijkstra.Adjacency
  {c ℓ} (alg : DijkstraAlgebra c ℓ)
  where

open DijkstraAlgebra alg renaming (Carrier to Weight)

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin hiding (_≤_; compare)
open import Data.Nat hiding (compare)
open import Data.Nat.Properties using (strictTotalOrder)
import Data.Vec as V
open V using (Vec)
import Data.Matrix as M
open M using (Matrix; tabulate)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl)

open StrictTotalOrder strictTotalOrder using (compare)

data Adj : ℕ → Set c where
  □ : Adj (suc zero)
  ◲ : ∀ {n} (adj : Adj n) (l : Vec Weight n) (t : Vec Weight n) → Adj (suc n)

transpose : ∀ {n} → Adj n → Adj n
transpose □           = □
transpose (◲ adj l t) = ◲ (transpose adj) t l

lookup : ∀ {n} → Fin n → Fin n → Adj n → Weight
lookup zero     zero     adj        = 1#
lookup i        (suc ()) □
lookup (suc ()) j        □
lookup zero     (suc j) (◲ adj l t) = V.lookup j t
lookup (suc i)  zero    (◲ adj l t) = V.lookup i l
lookup (suc i)  (suc j) (◲ adj l t) = lookup i j adj

toMatrix : ∀ {n} → Adj n → Matrix Weight n n
toMatrix adj = M.tabulate (λ i j → lookup i j adj)
