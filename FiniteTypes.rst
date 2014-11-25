============
Finite types
============

Finite types in SSreflect
-------------------------

In the `SSreflect library <http://ssr.msr-inria.inria.fr/doc/ssreflect-1.5/>`_, a finite type is represented as a list (more specifically, a sequence from SSreflect's ``seq`` library) together with a proof that it contains no duplicates. This condition is expressed in Coq as:

.. code:: coq

    Definition axiom e := \forall x : T, count_mem x e = 1.

As an example (taken from `An introduction to small scale reflection in Coq <http://jfr.unibo.it/article/view/1979>`_), *booleans* form a finite type by listing all possible values of the type and showing that no value occurs twice:

.. code:: coq

    Lemma bool_enumP : Finite.axiom [:: true; false]
    Proof. by case. Qed.

Other primitive finite types are the unit type and bounded ordinals (i.e. the set of all natural numbers smaller than some natural number).

Finite types can be combined to give new finite types by the following constructions:

- an option (or ``Maybe``) type parameterised over a finite type is a finite type;
- the *product* of two finite types is a finite type;
- the *sum* of two finite types is a finite type;
- *functions* with a finite type as their domain are completely characterised by a list of ``(x, f x)`` pairs and therefore finite in a sense---see the `finfun module <http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/MathComp.finfun.html>`_ which is now part of the Mathematical Components library.

Constructions of finite types *not* included in the ``SSreflect`` library:

- the functions from a finite domain into a finite codomain form a finite type;
- the powerset of a finite type is a finite type (Q: does it reside "one level up" in the type hierarchy?)

Ideas
-----

When each finite type is tagged with its cardinality, we can track the cardinality of finite types through finite type constructions (Example: type ``M`` has cardinality ``|M|`` and type ``N`` has cardinality ``|N|``. Then ``M + N`` has cardinality ``|M| + |N|``, and ``M × N`` has cardinality ``|M| |N|``.)

Other possible representations include:

- efficient set data structures like AVL trees---unfortunately these tend to require and ordering, and we would like to allow the construction of finite sets for as many types as possible;
- as lists where the elements are unique by construction using Agda's induction-recursion facilities.
