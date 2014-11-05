Part III project proposals
==========================

Graph library for Agda
----------------------

The Agda standard library currently lacks a graph module. The purpose of this project is to implement and prove correct a number of standard graph algorithms like Dijkstra's. This will require me to:

- Find a reasonably efficient purely functional representation for graphs. It should encode invariants as types so proofs can leverage Agda's type system to reason about graphs and graph algorithms;
- Translate textbook graph algorithms into a form that works in this purely functional setting; and
- Develop the correctness proofs.

I anticipate that the main challenges lie in finding a good representation for graphs in Agda and writing the correctness proofs. The data structures must be designed with the correctness proofs and algorithms in mind, so the steps described above will probably need to iterated rather than being completed one by one.

Open questions:

- Is this intended to be used primarily for programming (like fgl but with verified algorithms) or as a library of proofs (Isabelle- or Coq-style)?
- Should the proofs be done for a specific data type (for example an fgl-like representation) or against an abstract record (like a type class in Haskell)?

  - Pro data structure: potentially more straightforward (one fewer layer of abstraction); faster execution and type checking
  - Pro record: would require explicit assumptions; could have multiple representations implement the same "type class" and prove them correct in one go

- Which representation to use (if this is going to be a programming library)?

Generalised shortest path algorithms in Agda
--------------------------------------------

Current research into routing protocols seeks to formalise the assumptions made by routing algorithms in terms of the underlying algebraic structures, most notably variations and combinations of semirings.

This has lead to some surprising results -- for example, Dijkstra's algorithm requires much less structure from the underlying algebraic entity than previously thought.

The purpose of this project would be to prove one or more variants of the distributed Bellman-Ford algorithm or the Dijkstra algorithm correct while taking care to make as few assumptions as possible about the underlying algebraic structure. This will require me to:

- Translate the algebraic structures used in the analysis of routing protocols into Agda types and data structures. Some standard entities from abstract algebra already exist in Agda's standard library, others would have to be newly implemented;
- Find minimal sets of assumptions that make the routing algorithms correct; and
- Prove the correctness of the routing algorithms based on these assumptions in Agda.

Comments:

- I think that porting rie-1.0.v (to algebra-based correctness proof for Dijkstra in Coq) to Agda would make for a great two to three month project. But I don't see an obvious way of extending that into a part III dissertation.
