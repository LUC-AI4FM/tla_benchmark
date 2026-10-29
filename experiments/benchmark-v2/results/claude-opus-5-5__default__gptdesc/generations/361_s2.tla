---------------------------- MODULE LargeInitStates ----------------------------
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat

VARIABLES x, y, z

vars == <<x, y, z>>

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ z \in 0..N

Init ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ z \in 0..N

Next ==
    UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

THEOREM Spec => []Inv
THEOREM Spec => []TypeOK
=============================================================================