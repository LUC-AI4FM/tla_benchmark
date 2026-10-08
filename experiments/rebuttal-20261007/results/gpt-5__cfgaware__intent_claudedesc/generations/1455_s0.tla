--------------------------- MODULE SubsetOfPowersetSpec ---------------------------
EXTENDS Integers, Naturals

VARIABLES ok

AllTests ==
  /\ SUBSET (1..2) \subseteq SUBSET (1..3)
  /\ ~(SUBSET (1..3) \subseteq SUBSET (1..2))
  /\ LET R == 1..4 IN
     LET Rm == R \ {2} IN
       /\ SUBSET Rm \subseteq SUBSET R
       /\ ~(SUBSET R \subseteq SUBSET Rm)
  /\ LET A == {1} IN
     LET B == {1, 2} IN
     LET C == {1, 2, 3} IN
       /\ SUBSET A \subseteq SUBSET B
       /\ SUBSET B \subseteq SUBSET C
       /\ SUBSET A \subseteq SUBSET C
  /\ SUBSET {} \subseteq SUBSET {}
  /\ SUBSET {} \subseteq SUBSET {1}
  /\ SUBSET {} \subseteq SUBSET (1..3)
  /\ ~(SUBSET {1} \subseteq SUBSET {})
  /\ SUBSET {42} \subseteq SUBSET Int
  /\ SUBSET {42} \subseteq SUBSET Nat

Init == ok = AllTests

Next == UNCHANGED ok

TypeOK == ok \in BOOLEAN

Inv == TypeOK /\ ok

Invariant == Inv

Spec == Init /\ [][Next]_<<ok>>

=============================================================================