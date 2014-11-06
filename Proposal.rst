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

Generalised "big operators" in Agda
-----------------------------------

The goal of this project is to create an Agda library that describes "iterated big operators" uniformly, in the spirit of the ``bigops`` module in Coq's ``ssreflect`` library.

One application of such a module would be in reasoning about matrices, where big operator notation is commonly used.

Workplan:

- Get really good at Agda programming;
- Understand the mathematics behind big operators (what are the minimum assumptions, what do extra assumptions allow us to do?);
- Review previous work (``bigops``, ``explore``, ...);
- Design and build the library;
- Write the dissertation;
- Maybe publish the results.
