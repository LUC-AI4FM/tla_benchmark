----------------------------- MODULE PowersetSubsetSpec -----------------------------

EXTENDS Integers

CONSTANTS Dummy
ASSUME Dummy = TRUE

VARIABLES b

Init ==
  b = TRUE

Assertions ==
  /\ SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}
  /\ SUBSET (2..4) \subseteq SUBSET (1..5)
  /\ SUBSET Nat \subseteq SUBSET Int
  /\ SUBSET {} \subseteq SUBSET {1}
  /\ SUBSET (3..3) \subseteq SUBSET (3..3)
  /\ ~(SUBSET (1..5) \subseteq SUBSET (2..4))
  /\ ~(SUBSET {1, 4} \subseteq SUBSET {1, 2, 3})
  /\ ~(SUBSET Int \subseteq SUBSET Nat)

Next ==
  b' = Assertions

TypeInvariant ==
  b \in BOOLEAN

AlwaysTrue ==
  b = TRUE

Spec ==
  Init /\ [][Next]_b

=============================================================================