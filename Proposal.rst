Generalised big operators in Agda
=================================

Abstract
--------

"Big operator" notation is common in algebraic reasoning. It is a useful tool to express formulae in a succinct and abstract way, and reveals hidden symmetries that can immediately be exploited. In informal mathematics, the switch from small to big operators is often made without giving much thought to the implicit assumptions thereby made about the underlying algebra. In this project, I will implement a library for reasoning uniformly about big operators in the dependently typed programming language *cum* theorem proving environment, Agda. To demonstrate its usefulness, I will prove some standard results about properties of structures from abstract algebra.

Introduction
------------

In many areas of mathematics, "big operators" are a commonly used and versatile tool, and they provide a natural way to express an operation iterated over some set. Making big operators available in a formal theorem proving environment like Agda therefore allows for a natural style of algebraic reasoning.

An implementation of a big operator library exists for the theorem prover Coq [ref]. It relies on a number of ways to define structures and syntax the are specific to Coq and do not translate directly into Agda.

Along similar lines, an implementation of "explorations" in Agda exists which examines the relationship between foldable data structures and big operators [ref]. However, this work differs in several ways from what is proposed here. The library does not preserve the underlying algebraic structure of the operator and its carrier, instead relying on parametricity and free theorems to recover some laws based on type. It is not intended specifically towards simplifying proofs using big operators.

.. code:: haskell

    𝕄-mult-assoc : (p q r s : ℕ) →
                   (𝕄 p q × 𝕄 q r) × 𝕄 r s ≡ 𝕄 p q × (𝕄 q r × 𝕄 r s)
    𝕄-mult-assoc p q r s =
          (𝕄 p q × 𝕄 q r) × 𝕄 r s
        ≡⟨ ... ⟩
          ⨁ [ i <- q ] (𝕄 p q × 𝕄 q r) × 𝕄 r s
        ≡⟨ cong suc (+-comm' m n) ⟩
          suc (n + m)
        ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
          n + suc m
        ∎



Approach
--------

Outcomes
--------

The goal of this project is to create an Agda library that describes "iterated big operators" uniformly, in the spirit of the ``bigops`` module in Coq's ``ssreflect`` library.

One application of such a module would be in reasoning about matrices, where big operator notation is commonly used.

Workplan
--------

In order to design and implement such a library in Agda, I will have to become proficient in reading and writing Agda code. This entails learning how program with dependent types and put them to good use, and how code is structured and written idiomatically in Agda. This is the "technical" or "engineering" requirement for this project to be successful.

I will also have to acquire a good understanding of the mathematics of big operators. This involves finding answers to questions such as, 'what are the minimum requirements for a small operator and a carrier set so a big operator can automatically be derived from it?', and exploring what additional rules governing the big operator can be derived from properties of the underlying algebra.

My review of previous work on the mathematics and implementation of big operators has already begun, and I will expand this survey further.

The actual library will have to be designed and implemented. Given my limited exposure to Agda and its module system so far, this will probably be an iterative process.

The final piece 

- Understand the mathematics behind big operators (what are the minimum assumptions, what do extra assumptions allow us to do?);
- Review previous work (``bigops``, ``explore``, ...);
- Design and build the library;
- Write the dissertation;
- Maybe publish the results.
