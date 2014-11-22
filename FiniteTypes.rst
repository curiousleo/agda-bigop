===================
Finite Types in Coq
===================

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
- the type of all *functions* with a finite type as their domain is a finite type as it is completely characterised by a list of ``(x, f x)`` pairs---see the `finfun module <http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/MathComp.finfun.html>`_ which is now part of the Mathematical Components library.
