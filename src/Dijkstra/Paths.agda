module Dijkstra.Paths where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; fromℕ; zero; suc)
open import Data.List
open import Data.Nat hiding (compare)
open import Data.Nat.Properties using (strictTotalOrder)
open import Data.Product using (_×_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl)

open StrictTotalOrder strictTotalOrder using (compare)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

record Path {n} (i j : Fin n) : Set where
  constructor via
  field
    mids : List (Fin n)

  edges : List (Fin n × Fin n)
  edges = zip (i ∷ mids) (mids ∷ʳ j)

data Paths : ℕ → Set where
  □ : Paths 1
  ◰ : ∀ {n} (adj : Paths n) (from : ∀ i → Path i (fromℕ n)) (into : ∀ j → Path (fromℕ n) j) → Paths (suc n)

private

  contradiction : ∀ {a} {b} → a ≤ b → suc b ≤ a → ⊥
  contradiction {zero}  {b}     a≤b       ()
  contradiction {suc a} {zero}  ()        sb≤a
  contradiction {suc a} {suc b} (s≤s a≤b) (s≤s sb≤a) = contradiction a≤b sb≤a

lookup-from≤ : ∀ {m n} → m ≤ n → (i : Fin (suc m)) → Paths (suc n) → Path i (fromℕ m)
lookup-from≤ {zero}  {n}      z≤n       zero     adj = via []
lookup-from≤ {zero}  {n}      z≤n       (suc ()) adj
lookup-from≤ {suc m} {suc n}  (s≤s m≤n) i        (◰ adj from into) with compare m n
lookup-from≤ {suc m} {suc n}  (s≤s m≤n) i        (◰ adj from into) | tri<  a ¬b    ¬c = lookup-from≤ a i adj
lookup-from≤ {suc m} {suc .m} (s≤s m≤n) i        (◰ adj from into) | tri≈ ¬a  refl ¬c = from i
lookup-from≤ {suc m} {suc n}  (s≤s m≤n) i        (◰ adj from into) | tri> ¬a ¬b     c = ⊥-elim (contradiction m≤n c)

lookup-into≤ : ∀ {m n} → m ≤ n → (j : Fin (suc m)) → Paths (suc n) → Path (fromℕ m) j
lookup-into≤ {zero}  {n}      z≤n       zero     adj = via []
lookup-into≤ {zero}  {n}      z≤n       (suc ()) adj
lookup-into≤ {suc m} {suc n}  (s≤s m≤n) j        (◰ adj from into) with compare m n
lookup-into≤ {suc m} {suc n}  (s≤s m≤n) j        (◰ adj from into) | tri<  a ¬b    ¬c = lookup-into≤ a j adj
lookup-into≤ {suc m} {suc .m} (s≤s m≤n) j        (◰ adj from into) | tri≈ ¬a  refl ¬c = into j
lookup-into≤ {suc m} {suc n}  (s≤s m≤n) j        (◰ adj from into) | tri> ¬a ¬b     c = ⊥-elim (contradiction m≤n c)

lookup-from : ∀ {n} → (i : Fin (suc n)) → Paths (suc n) → Path i (fromℕ n)
lookup-from = lookup-from≤ ≤-refl

lookup-into : ∀ {n} → (j : Fin (suc n)) → Paths (suc n) → Path (fromℕ n) j
lookup-into = lookup-into≤ ≤-refl
