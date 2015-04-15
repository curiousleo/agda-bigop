{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Bigop.Lemmas where

  import Relation.Binary.EqReasoning as EqR

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core using (Op₂)

  open import Data.Empty
  open import Data.Unit.Base hiding (_≤_)
  open import Data.Product hiding (map; Σ-syntax)
  open import Data.Fin hiding (fold; fold′) renaming (_+_ to _+F_; _≤_ to _≤F_)
  open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
  open import Data.Nat hiding (fold) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
  open import Data.List.Base

  open import Level using (Level)
  
  open import Relation.Unary
  open import Relation.Nullary
  open import Relation.Nullary.Decidable hiding (map)
  open import Relation.Nullary.Negation

  open import Function

  module Core {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

    open Monoid M renaming (Carrier to R)

    fold : (I → R) → List I → R
    fold f = foldr (λ x y → (f x) ∙ y) ε

    Σ-syntax : _
    Σ-syntax = fold

    syntax Σ-syntax (λ x → e) v = Σ[ x ← v $ e ]

    Π-syntax : _
    Π-syntax = fold

    syntax Π-syntax (λ x → e) v = Π[ x ← v $ e ]

    ⨁-syntax : _
    ⨁-syntax = fold

    syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v $ e ]

    ⨂-syntax : _
    ⨂-syntax = fold

    syntax ⨂-syntax (λ x → e) v = ⨂[ x ← v $ e ]

  range : ∀ {from to} → from ≤ to → List (Fin to)
  range (z≤n {zero})          = []
  range (z≤n {suc to})        = zero ∷ map suc (range (z≤n {to}))
  range (s≤s {from} {to} f≤t) = map suc (range f≤t)

  fromLenF : (from len : ℕ) → List (Fin (from +ℕ len))
  fromLenF from len = range {from} {from + len} (m≤m+n from len)
    where
      open Data.Nat
      open import Data.Nat.Properties.Simple

      ≤-refl : ∀ n → n ≤ n
      ≤-refl zero    = z≤n
      ≤-refl (suc n) = s≤s (≤-refl n)

      m≤m+n : ∀ m n → m ≤ m + n
      m≤m+n zero n = z≤n
      m≤m+n (suc m) zero rewrite +-comm (suc m) zero = ≤-refl (suc m)
      m≤m+n (suc m) (suc n) = s≤s (m≤m+n m (suc n))

  fromLenℕ : ℕ → ℕ → List ℕ
  fromLenℕ from zero = []
  fromLenℕ from (suc len) = from ∷ fromLenℕ (suc from) len

  downFromLenℕ : ℕ → ℕ → List ℕ
  downFromLenℕ zero       zero      = []
  downFromLenℕ (suc _)    zero      = []
  downFromLenℕ zero       (suc len) = [ zero ]
  downFromLenℕ (suc from) (suc len) = suc from ∷ downFromLenℕ from len

  module _ where
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning

    _…+_ = fromLenℕ
    _…-_ = downFromLenℕ

    _…_ : ℕ → ℕ → List ℕ
    m … n = m …+ (suc n ∸ m)

    _…↓_ : ℕ → ℕ → List ℕ
    m …↓ n = m …- (suc m ∸ n)

{-
    …-lemma : ∀ m n → m …↓ n ≡ reverse (n … m)
    …-lemma zero zero = refl
    …-lemma zero (suc n) = begin
      downFromLenℕ zero (0 ∸ n)
        ≡⟨ cong (downFromLenℕ zero) (0∸n≡0 n) ⟩
      reverse []
        ≡⟨ cong reverse (sym (begin
          fromLenℕ (suc n) (0 ∸ n)
            ≡⟨ cong (fromLenℕ (suc n)) (0∸n≡0 n) ⟩
          [] ∎)) ⟩
      reverse (suc n … zero) ∎
      where

        0∸n≡0 : ∀ n → 0 ∸ n ≡ 0
        0∸n≡0 zero    = refl
        0∸n≡0 (suc n) = refl

    …-lemma (suc m) n = {!!}
-}

    open import Relation.Unary
    open import Relation.Nullary
    open import Relation.Nullary.Decidable using (⌊_⌋)
    open import Level using (zero)
    open import Data.Empty

    DecPred : ∀ {i} (I : Set i) {ℓ} → Set _
    DecPred I {ℓ} = Σ (Pred I ℓ) Decidable

    infixl 6 _∣_ _∥_

    _∣_ : ∀ {i} {I : Set i} {ℓ} → List I → DecPred I {ℓ} → List I
--  is ∣ (_ , dec) = filter (λ i → ⌊ dec i ⌋) is
    []       ∣ (_ , dec) = []
    (i ∷ is) ∣ (_ , dec) with dec i
    (i ∷ is) ∣ (p , dec) | yes _ = i ∷ is ∣ (p , dec)
    (i ∷ is) ∣ (p , dec) | no  _ =     is ∣ (p , dec)

    _∥_ : ∀ {i} {I : Set i} {ℓ} {P : Pred I ℓ} → List I → Decidable P → List I
    [] ∥ dec = []
    (i ∷ is) ∥ dec with dec i
    (i ∷ is) ∥ dec | yes _ = i ∷ is ∥ dec
    (i ∷ is) ∥ dec | no  _ =     is ∥ dec

    data Even : Pred ℕ Level.zero where
      zero-even : Even ℕ.zero
      ss-even : ∀ {n} → Even n → Even (suc (suc n))

    even : Decidable Even
    even 0 = yes zero-even
    even 1 = no (λ ())
    even (suc (suc n)) with even n
    even (suc (suc n)) | yes p = yes (ss-even p)
    even (suc (suc n)) | no ¬p = no (ss-odd ¬p)
      where
        ss-odd : ∀ {n} → ¬ Even n → ¬ Even (suc (suc n))
        ss-odd ¬ps (ss-even p) = ⊥-elim (¬ps p)

    data Odd : Pred ℕ Level.zero  where
      one-odd : Odd 1
      ss-odd : ∀ {n} → Odd n → Odd (suc (suc n))

    odd : Decidable Odd
    odd 0 = no (λ ())
    odd 1 = yes one-odd
    odd (suc (suc n)) with odd n
    odd (suc (suc n)) | yes p = yes (ss-odd p)
    odd (suc (suc n)) | no ¬p = no (ss-even′ ¬p)
      where
        ss-even′ : ∀ {n} → ¬ Odd n → ¬ Odd (suc (suc n))
        ss-even′ ¬ps (ss-odd p) = ⊥-elim (¬ps p)

    even′ : DecPred ℕ {Level.zero}
    even′ = Even , even

    odd′ : DecPred ℕ {Level.zero}
    odd′ = ∁ (proj₁ even′) , ¬? ∘ proj₂ even′
      where
        open import Relation.Nullary.Negation

    test-even′ : 1 … 6 ∣ even′ ≡ 2 ∷ 4 ∷ 6 ∷ []
    test-even′ = refl

    test-odd′ : 1 … 6 ∣ odd′ ≡ 1 ∷ 3 ∷ 5 ∷ []
    test-odd′ = refl
    
    test-even : 1 … 6 ∥ even ≡ 2 ∷ 4 ∷ 6 ∷ []
    test-even = refl

    test-odd : 1 … 6 ∥ odd ≡ 1 ∷ 3 ∷ 5 ∷ []
    test-odd = refl

  module RangeLemmas {i} {I : Set i} {ℓ : Level} where
    open import Relation.Binary.PropositionalEquality hiding ([_])
    open import Data.Nat.Base
    open import Data.Nat.Properties.Simple

    open ≡-Reasoning

    suc-lemma : ∀ m n → map suc (fromLenℕ m n) ≡ fromLenℕ (suc m) n
    suc-lemma m zero    = refl
    suc-lemma m (suc n) = cong (_∷_ (suc m)) (suc-lemma (suc m) n)

    suc-head-lemma : ∀ m n → m ∷ (fromLenℕ (suc m) n) ≡ fromLenℕ m (suc n)
    suc-head-lemma m n = refl

    suc-last-lemma : ∀ m n → fromLenℕ m (suc n) ≡ (fromLenℕ m n) ∷ʳ (m + n)
    suc-last-lemma m zero = cong (_∷ʳ_ []) $ +-comm zero m
    suc-last-lemma m (suc n) = begin
      m ∷ fromLenℕ (suc m) (suc n)
        ≡⟨ cong (_∷_ m) $ suc-last-lemma (suc m) n ⟩
      m ∷ (fromLenℕ (suc m) n) ∷ʳ suc m + n
        ≡⟨ cong (_∷ʳ_ $ fromLenℕ m (suc n)) $ sym $ +-suc m n ⟩
      fromLenℕ m (suc n) ∷ʳ m + suc n ∎

    head-yes : ∀ {P : Pred I ℓ} x xs (p : Decidable P) →
               True (p x) → (x ∷ xs) ∥ p ≡ x ∷ (xs ∥ p)
    head-yes x xs p t with p x
    head-yes x xs p t  | yes _ = refl
    head-yes x xs p () | no  _

    head-no : ∀ {P : Pred I ℓ} x xs (p : Decidable P) →
              False (p x) → (x ∷ xs) ∥ p ≡ xs ∥ p
    head-no x xs p f with p x
    head-no x xs p () | yes _
    head-no x xs p tt | no  _ = refl

    last-no : ∀ {P : Pred I ℓ} xs x (p : Decidable P) →
              False (p x) → (xs ∷ʳ x) ∥ p ≡ xs ∥ p
    last-no     xs       x p f with p x
    last-no     xs       x p () | yes _
    last-no {P} []       x p tt | no ¬p =     head-no {P} x [] p (fromWitnessFalse ¬p)
    last-no     (y ∷ ys) x p tt | no ¬p with p y
    last-no     (y ∷ ys) x p tt | no ¬p | yes _ =
                                   cong (_∷_ y) $ last-no ys x p (fromWitnessFalse ¬p)
    last-no     (y ∷ ys) x p tt | no ¬p | no  _ = last-no ys x p (fromWitnessFalse ¬p)

    last-yes : ∀ {P : Pred I ℓ} xs x (p : Decidable P) →
               True (p x) → (xs ∷ʳ x) ∥ p ≡ (xs ∥ p) ∷ʳ x
    last-yes xs x p t with p x
    last-yes [] x p tt | yes q =               head-yes x [] p (fromWitness q)
    last-yes (y ∷ ys) x p tt | yes q with p y
    last-yes (y ∷ ys) x p tt | yes q | yes _ =
                                cong (_∷_ y) $ last-yes ys x p (fromWitness q)
    last-yes (y ∷ ys) x p tt | yes q | no  _ = last-yes ys x p (fromWitness q)
    last-yes xs x p () | no  _

    postulate
      uniqueℕ : ∀ m n k → m ≤ k → k ≤ n → fromLenℕ m n ∥ _≟_ k ≡ [ k ]
      uniqueF : ∀ m n k → m ≤ toℕ k → toℕ k ≤ (m +ℕ n) → fromLenF m n ∥ _≟F_ k ≡ [ k ]

  module MonoidLemmas
         {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

    open Monoid M renaming (Carrier to R)
    open EqR setoid

    open Core M

    Σ-head : (f : I → R) (x : I) (xs : List I) →
             fold f (x ∷ xs) ≈ f x ∙ fold f xs
    Σ-head _ _ _ = refl

    Σ-last : (f : I → R) (x : I) (xs : List I) →
             fold f (xs ∷ʳ x) ≈ fold f xs ∙ f x
    Σ-last f x [] = begin
      f x ∙ ε  ≈⟨ proj₂ identity _ ⟩
      f x      ≈⟨ sym $ proj₁ identity _ ⟩
      ε ∙ f x  ∎
    Σ-last f x (y ∷ ys) = begin
      f y ∙ fold f (ys ∷ʳ x)   ≈⟨ ∙-cong refl (Σ-last f x ys) ⟩
      f y ∙ (fold f ys ∙ f x)  ≈⟨ sym $ assoc _ _ _ ⟩
      (f y ∙ fold f ys) ∙ f x  ∎

    Σ-shift : (f : I → R) (x : I) (xs : List I) →
              f x ≈ ε → fold f (x ∷ xs) ≈ fold f xs
    Σ-shift f x xs fx≈ε = begin
      f x ∙ fold f xs  ≈⟨ ∙-cong fx≈ε refl ⟩
      ε ∙ fold f xs    ≈⟨ proj₁ identity _ ⟩
      fold f xs        ∎

    Σ-zero : (xs : List I) → fold (const ε) xs ≈ ε
    Σ-zero [] = refl
    Σ-zero (x ∷ xs) = trans (proj₁ identity _) (Σ-zero xs)

    Σ-cong′ : {f g : I → R} → (∀ x → f x ≈ g x) → (is : List I) →
              fold f is ≈ fold g is
    Σ-cong′         f≗g []       = refl
    Σ-cong′ {f} {g} f≗g (i ∷ is) = begin
      f i ∙ fold f is
        ≈⟨ f≗g i ⟨ ∙-cong ⟩ Σ-cong′ {f} {g} f≗g is ⟩
      g i ∙ fold g is ∎

    -- Σ-cong could be generalised further to f : I → R, g : J → R, h : I → J
    Σ-cong : {f g : I → R} (h : I → I) → (∀ x → f x ≈ g (h x)) → (is : List I) →
             fold f is ≈ fold g (map h is)
    Σ-cong         h f≗gh []       = refl
    Σ-cong {f} {g} h f≗gh (i ∷ is) = begin
      f i ∙ fold f is
        ≈⟨ f≗gh i ⟨ ∙-cong ⟩ Σ-cong {f} {g} h f≗gh is ⟩
      g (h i) ∙ fold g (map h is) ∎

    import Relation.Binary.PropositionalEquality as P

    Σ-cong″ : {f g : I → R} → (∀ x → f x ≈ g x) → {is : List I} → {js : List I} → is P.≡ js →
              fold f is ≈ fold g js
    Σ-cong″ fx≈gx {[]} P.refl = refl
    Σ-cong″ {f} {g} fx≈gx {i ∷ is} P.refl = begin
      f i ∙ fold f is
        ≈⟨ ∙-cong (fx≈gx i) (Σ-cong″ fx≈gx (P.refl {x = is})) ⟩
      g i ∙ fold g is ∎

    postulate
      Σ-cong-P : ∀ {ℓ} {f g : I → R} {P : Pred I ℓ} (is : List I) (p : Decidable P) →
                 (∀ i → (P i) → f i ≈ g i) → fold f (is ∥ p) ≈ fold g (is ∥ p)

  module CommutativeMonoidLemmas
         {c ℓ} (M : CommutativeMonoid c ℓ) {i} {I : Set i} {j} {J : Set j} where

    open CommutativeMonoid M renaming (Carrier to R)
    open EqR setoid

    open Core monoid

    open MonoidLemmas monoid

{-
    Σ-reverse : (f : I → R) (is : List I) →
                fold f is ≈ fold f (reverse is)
    Σ-reverse f []       = refl
    Σ-reverse f (i ∷ is) = begin
      f i ∙ fold f is
        ≈⟨ comm _ _ ⟩
      fold f is ∙ f i
        ≈⟨ ∙-cong (Σ-reverse f is) refl ⟩
      fold f (reverse is) ∙ f i
        ≈⟨ sym (Σ-last f i (reverse is)) ⟩
      fold f (reverse is ∷ʳ i)
        ≈⟨ Σ-cong″ (λ x → refl) (P.sym (reverse-∷ʳ i is)) ⟩ -- ≡⟨ P.cong (fold f) (P.sym (reverse-∷ʳ i is)) ⟩
      fold f (reverse (i ∷ is)) ∎
      where
        import Relation.Binary.PropositionalEquality as P
        open P.≡-Reasoning renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
{-
        reverse′ : ∀ {a} {A : Set a} → List A → List A
        reverse′ [] = []
        reverse′ (x ∷ xs) = reverse′ xs ∷ʳ x

        reverse-reverse′ : ∀ {a} {A : Set a} (xs : List A) → reverse xs P.≡ reverse′ xs
        reverse-reverse′ [] = P.refl
        reverse-reverse′ (x ∷ xs) = start
          foldl (λ rev x → x ∷ rev) (x ∷ []) xs
            ≣⟨ {!reverse (x ∷ xs)!} ⟩
          reverse xs ++ [ x ]
            ≣⟨ P.cong₂ _++_ (reverse-reverse′ xs) P.refl ⟩
          reverse′ xs ∷ʳ x □
-}
        reverse-∷ʳ : ∀ (i : I) is → reverse (i ∷ is) P.≡ reverse is ∷ʳ i
        reverse-∷ʳ i []       = P.refl
        reverse-∷ʳ i (j ∷ js) = start
          reverse (i ∷ j ∷ js)
            ≣⟨ {!reverse (i ∷ j ∷ js)!} ⟩
          reverse (j ∷ js) ∷ʳ i □
-}

    Σ-lift : (f g : I → R) (is : List I) →
             fold f is ∙ fold g is ≈ fold (λ i → f i ∙ g i) is
           -- Σ[ k ← is $ f k ] + Σ[ k ← is $ g k ] ≡ Σ[ k ← is $ f k + g k ]
    Σ-lift f g [] = proj₁ identity _
    Σ-lift f g (i ∷ is) = begin
      (f i ∙ fold f is) ∙ (g i ∙ fold g is)
        ≈⟨ assoc (f i) (fold f is) (g i ∙ fold g is) ⟩
      f i ∙ (fold f is ∙ (g i ∙ fold g is))
        ≈⟨ refl {f i} ⟨ ∙-cong ⟩ lemma ⟩
      f i ∙ (g i ∙ fold (λ i → f i ∙ g i) is)
        ≈⟨ sym (assoc (f i) (g i) (fold (λ i → f i ∙ g i) is)) ⟩
      (f i ∙ g i) ∙ fold (λ i → f i ∙ g i) is ∎
      where
        lemma : fold f is ∙ (g i ∙ fold g is) ≈
                g i ∙ fold (λ i → f i ∙ g i) is
        lemma = begin
          fold f is ∙ (g i ∙ fold g is)
            ≈⟨ sym (assoc (fold f is) (g i) (fold g is)) ⟩
          (fold f is ∙ g i) ∙ fold g is
            ≈⟨ comm (fold f is) (g i) ⟨ ∙-cong ⟩ refl ⟩
          (g i ∙ fold f is) ∙ fold g is
            ≈⟨ assoc (g i) (fold f is) (fold g is) ⟩
          g i ∙ (fold f is ∙ fold g is)
            ≈⟨ (refl {g i}) ⟨ ∙-cong ⟩ Σ-lift f g is ⟩
          g i ∙ fold (λ i → f i ∙ g i) is ∎

    Σ-swap : (f : J → I → R) (js : List J) (is : List I) →
             fold (λ j → fold (f j) is) js ≈ fold (λ i → fold (flip f i) js) is
    Σ-swap f [] ys = sym (Σ-zero ys)
    Σ-swap f xs [] = Σ-zero xs
    Σ-swap f (x ∷ xs) ys = begin
      fold (f x) ys ∙ fold (λ j → fold (f j) ys) xs
        ≈⟨ refl {fold (f x) ys} ⟨ ∙-cong ⟩ Σ-swap f xs ys ⟩
      fold (f x) ys ∙ fold (λ i → fold (flip f i) xs) ys
        ≈⟨ Σ-lift (f x) (λ i → fold (flip f i) xs) ys ⟩
      fold (λ i → f x i ∙ fold (flip f i) xs) ys ∎

    ∁-dec : ∀ {ℓ} {P : Pred I ℓ} → Decidable P → Decidable (∁ P)
    ∁-dec p x with p x
    ∁-dec p x | yes q = no (λ ¬q → ¬q q)
    ∁-dec p x | no ¬q = yes (λ q → ¬q q)

    postulate
      Σ-split : ∀ {ℓ} {P : Pred I ℓ} → (f : I → R) (is : List I) (p : Decidable P) →
                fold f is ≈ fold f (is ∥ p) ∙ fold f (is ∥ ∁-dec p)

{-
    Σ-split : ∀ {ℓ} {P : Pred I ℓ} → (f : I → R) (is : List I) (p : Decidable P) →
              fold f is ≈ fold f (is ∥ p) ∙ fold f (is ∥ ∁-dec p)
    Σ-split f [] p = {!!} -- proj₁ identity _
    Σ-split f (i ∷ is) p with p i
    ... | yes q = {!!}
    ... | no ¬q = {!!}
-}

  module SemiringWithoutOneLemmas
         {c ℓ} (S : SemiringWithoutOne c ℓ) {i} {I : Set i} where

    open SemiringWithoutOne S
      renaming (Carrier to R; zero to *-zero)
    open EqR setoid

    open Core +-monoid

    open CommutativeMonoidLemmas +-commutativeMonoid {I = I}

    Σ-distrˡ : (f : I → R) (x : R) (is : List I) →
               x * fold f is ≈ fold (λ k → x * (f k)) is
    Σ-distrˡ f x [] = proj₂ *-zero x
    Σ-distrˡ f x (n ∷ ns) =
      begin
        x * (f n + fold f ns)
          ≈⟨ proj₁ distrib x (f n) (fold f ns) ⟩
        (x * f n) + (x * fold f ns)
          ≈⟨ refl {x * f n} ⟨ +-cong ⟩ Σ-distrˡ f x ns ⟩
        (x * f n) + fold ((_*_ x) ∘ f) ns
      ∎

    Σ-distrʳ : (f : I → R) (x : R) (is : List I) →
               fold f is * x ≈ fold (λ k → (f k) * x) is
    Σ-distrʳ f x [] = proj₁ *-zero x
    Σ-distrʳ f x (n ∷ ns) =
      begin
        (f n + fold f ns) * x
          ≈⟨ proj₂ distrib x (f n) (fold f ns) ⟩
        (f n * x) + (fold f ns * x)
          ≈⟨ refl {f n * x} ⟨ +-cong ⟩ Σ-distrʳ f x ns ⟩
        (f n * x) + fold (λ k → (f k) * x) ns
      ∎
{-
  module SemiringWithoutAnnihilatingZeroLemmas
         {c ℓ} (S : SemiringWithoutAnnihilatingZero c ℓ) {i} {I : Set i} {j} {J : Set j} where

    open SemiringWithoutAnnihilatingZero S
      renaming (Carrier to R)
    open EqR setoid

    open Core +-monoid using (Σ-syntax)
    open Core *-monoid using (Π-syntax)

    open CommutativeMonoidLemmas +-commutativeMonoid {I = I}

    interchange : (f : I → J → R) (is : List I) (js : List J) →
                  Σ[ i ← is $ Π[ j ← js $ f i j ] ] ≈ Σ[ j ← js $ Π[ i ← is $ f i j ] ]
    interchange f [] js = {!Σ-syntax (λ j → Π-syntax (λ i → f i j) []) js!}
    interchange f (x ∷ is) js = {!!}
    -- Σ[ i ← is $ Π[ j ← js $ f i j ] ] ≈ Σ[ j ← js $ Π[ i ← is $ f i j ] ]
    --    f i₀ j₀ * f i₀ j₁ * f i₀ j₂ + f i₁ j₀ * f i₁ j₁ * f i₁ j₂
    -- == f i₀ j₀ * f i₁ j₀ + f i₀ j₁ * f i₁ j₁ + f i₀ j₂ * f i₁ j₂
-}
