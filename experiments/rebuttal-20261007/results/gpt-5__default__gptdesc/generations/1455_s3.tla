----------------------------- MODULE PowersetSubsetSpec -----------------------------

EXTENDS Integers

VARIABLES b

Init ==
  b = TRUE

SubsetAssertions ==
  /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
  /\ ~((SUBSET {1, 2, 3}) \subseteq (SUBSET {1, 2}))
  /\ ((SUBSET (0..5)) \subseteq (SUBSET ((-1)..5)))
  /\ ~((SUBSET (0..5)) \subseteq (SUBSET (1..5)))
  /\ ((SUBSET ((-3)..3)) \subseteq (SUBSET ((-5)..5)))
  /\ ~((SUBSET ((-5)..5)) \subseteq (SUBSET ((-3)..3)))
  /\ ((SUBSET Nat) \subseteq (SUBSET Int))
  /\ ~((SUBSET Int) \subseteq (SUBSET Nat))

Next ==
  b' = SubsetAssertions

Invariant ==
  (b = TRUE) /\ (b \in BOOLEAN)

Spec ==
  Init /\ [] [Next]_b

=============================================================================