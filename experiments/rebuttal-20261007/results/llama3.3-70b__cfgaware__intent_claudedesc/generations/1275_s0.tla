---------------------------- MODULE DemoInitPred --------------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x

Init == (x \in {0} /\ x < 1)

Next == FALSE

Spec == Init /\ [][Next]_x

Inv == x < 1

THEOREM Spec => []Inv
=============================================================================