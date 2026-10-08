---------------------------- MODULE MutableSubset ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Universe
VARIABLE subset

TypeOK == Universe = {1, 2, 3} /\ subset \subseteq Universe

Init ==
  /\ Universe = {1, 2, 3}
  /\ subset \subset Universe

Next ==
  /\ Universe' = Universe
  /\ subset' \subseteq Universe

Inv == TypeOK

=============================================================================