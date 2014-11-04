Part III project proposals
==========================

Graph library for Agda
----------------------

Agda is a purely functional dependently-typed programming language, based on Martin-Löf type theory, *cum* theorem proving environment. In Agda, theorems are expressed as types and proofs as terms inhabiting those types.

The Agda standard library currently lacks a graph module. The purpose of this project is to implement and prove correct a number of standard graph algorithms like Dijkstra's. This will require me to:

- Find a reasonably efficient purely functional representation for graphs. It should encode invariants as types so proofs can leverage Agda's type system to reason about graphs and graph algorithms;
- Translate textbook graph algorithms into a form that works in this purely functional setting; and
- Develop the correctness proofs.

I anticipate that the main challenges lie in finding a good representation for graphs in Agda and writing the correctness proofs. The data structures must be designed with the correctness proofs and algorithms in mind, so the steps described above will probably need to iterated rather than being completed one by one.

Generalised shortest path algorithms in Agda
--------------------------------------------

Current research into routing protocols seeks to formalise the assumptions made by routing algorithms in terms of the underlying algebraic structures, most notably variations and combinations of semirings.

This has lead to some surprising results -- for example, Dijkstra's algorithm requires much less structure from the underlying algebraic entity than previously thought.

The purpose of this project would be to prove one or more variants of the distributed Bellman-Ford algorithm or the Dijkstra algorithm correct while taking care to make as few assumptions as possible about the underlying algebraic structure. This will require me to:

- Translate the algebraic structures used in the analysis of routing protocols into Agda types and data structures. Some standard entities from abstract algebra already exist in Agda's standard library, others would have to be newly implemented;
- Find minimal sets of assumptions that make the routing algorithms correct; and
- Prove the correctness of the routing algorithms based on these assumptions in Agda.
