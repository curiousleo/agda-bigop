======================================
Bigop: a big operator library for Agda
======================================

This library implements iterated big operators (think Σ and ⋃) in Agda. It is
mainly inspired by the ``bigop.v`` module in Coq's `Mathematical Components
library`_.

.. _`Mathematical Components library`:
   http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/MathComp.bigop.html

Requirements
============

Agda and a copy of the standard library are required. The code has been
tested with Agda 2.4.2.2 and the corresponding version of the standard
library. Agda's `readme`_ contains installation instructions for various
platforms. You will need to edit the agda-mode search path in order to use
the standard library when editing Agda files in Emacs (the Agda `readme`_
cover this too).

The procedure for this library is the same: in order to use it, all you need
to do is download it and add it to agda-mode's search path.

.. _readme: https://github.com/agda/agda/blob/2.4.2.2/README.md

Overview
========

The project contains three proofs which make use of this library and serve as
examples: ``GaussProofs.agda``, ``BinomialTheorem.agda`` and
``SemiringProof.agda``.

In order to use the library, a monoid or some structure that contains a
monoid is required. The library then lets you reason about the big operator
built by iterating the monoid's operator over a list.

Here is an overview of the imports required to get started:

* *Bigop.Core.Fold* contains syntax definitions which allow you to write sums
  as ``Σ[ x ← xs ] x * x`` and iterated *and* as ``⋀[ x ← xs ] x ∨ y``. The
  syntax is just intended to make propositions and proofs easier to read; the
  syntax definitions are just synonyms. It is up to the user to pick a syntax
  that makes sense to use with the  monoid at hand.

* *Bigop.Properties.XXX* provides lemmas about the algebraic structure XXX.
  Currently, lemmas exist for monoids (*Bigop.Properties.Monoid*),
  commutative monoids (*Bigop.Properties.CommutativeMonoid*), "semirings
  without one" (*Bigop.Properties.SemiringWithoutOne*) and Boolean algebras
  (*Bigop.Properties.BooleanAlgebra*). All modules take an appropriate
  algebraic structure as their argument. Stronger structures automatically
  inherit all lemmas from weaker structures---that is, all monoid lemmas are
  available via *Bigop.Properties.CommutativeMonoid* also.

  The recommended way to import those lemmas is, e.g. for a monoid called
  "+-monoid", ``module Σ = Bigop.Properties.Monoid +-monoid``. This avoid
  name clashes (the lemmas use common names like ``cong`` and ``map``).

* *Bigop.Interval.[Nat|Fin]* is usually also required in order to generate
  lists to iterate over. Both export the infix operators ``_…_`` and ``_…<_``
  which return an interval including and excluding the second argument,
  respectively. The functions defined in *Bigop.Interval.Nat* create lists of
  ℕs whereas *Bigop.Interval.Fin* creates Fin lists.
  *Bigop.Interval.Properties.[Nat|Fin]* contains lemmas about intervals
  created in this way.

* *Bigop.Filter* provides the operator ``_∥_`` which filters lists. The
  notation is meant to work well together with the interval and big operator
  syntax. *Bigop.Filter.Properties* contains lemmas about filters.
  *Bigop.Filter.Predicates* defines the decidable predicates ``even`` and
  ``odd``.

Usage
=====

::

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
