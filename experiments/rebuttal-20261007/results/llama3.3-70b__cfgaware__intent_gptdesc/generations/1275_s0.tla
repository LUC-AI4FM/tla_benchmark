---------------------------- MODULE SimpleStateVariable ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x

Init == (EXISTS v \in {0, 1} : x' = v) /\ x < 1

Next == x' = x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv
PROOF * Inv == x < 1 *

=============================================================================