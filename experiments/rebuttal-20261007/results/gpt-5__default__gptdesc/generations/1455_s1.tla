------------------------------ MODULE PowersetSubsetSpec ------------------------------

EXTENDS Integers

CONSTANTS UnusedConstant

VARIABLES b

Init ==
  b = TRUE

PowSubRelAssertions ==
  /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
  /\ ~(SUBSET {1, 2, 4} \subseteq SUBSET {1, 2, 3})
  /\ (SUBSET (1..3) \subseteq SUBSET (0..5))
  /\ ~(SUBSET (-2..2) \subseteq SUBSET (0..1))
  /\ (SUBSET Nat \subseteq SUBSET Int)
  /\ ~(SUBSET Int \subseteq SUBSET Nat)

Next ==
  b' = PowSubRelAssertions

Spec ==
  Init /\ [][Next]_b

Inv ==
  /\ b \in BOOLEAN
  /\ b = TRUE

=============================================================================