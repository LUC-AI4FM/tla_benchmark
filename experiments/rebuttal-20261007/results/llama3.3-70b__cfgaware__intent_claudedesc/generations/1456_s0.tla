---------------------------- MODULE SubsetExample ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Universe
VARIABLE subset, constantSet

Init ==
  /\ subset \subseteq {1, 2}
  /\ constantSet = {1, 2, 3}

Next ==
  /\ constantSet' = constantSet
  /\ subset' \subseteq constantSet

TypeOK == 
  /\ subset \subseteq Universe
  /\ constantSet \subseteq Universe

Inv == 
  /\ TypeOK
  /\ ENABLED (subset' \subseteq {1})

Universe == {1, 2, 3}

THEOREM Spec => []Inv
=============================================================================