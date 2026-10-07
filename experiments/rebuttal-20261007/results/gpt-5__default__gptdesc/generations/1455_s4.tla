------------------------------ MODULE PowersetSubsetTrivial ------------------------------

EXTENDS Naturals, Integers, TLC

CONSTANTS
  DummyConst

VARIABLES
  b

Init ==
  b = TRUE

Assertions ==
  /\ SUBSET {} \subseteq SUBSET {}
  /\ SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}
  /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
  /\ ~(SUBSET {1, 3} \subseteq SUBSET {1, 2})
  /\ SUBSET (1..3) \subseteq SUBSET (0..5)
  /\ ~(SUBSET (0..5) \subseteq SUBSET (1..3))
  /\ SUBSET Nat \subseteq SUBSET Int
  /\ ~(SUBSET Int \subseteq SUBSET Nat)
  /\ SUBSET {1, 2} \subseteq SUBSET (1..3)
  /\ ~(SUBSET {1, 4} \subseteq SUBSET (1..3))

Next ==
  b' = Assertions

Spec ==
  Init /\ []Next

TypeInvariant ==
  b \in BOOLEAN

AlwaysTrueInvariant ==
  b = TRUE

Invariant ==
  TypeInvariant /\ AlwaysTrueInvariant

=============================================================================