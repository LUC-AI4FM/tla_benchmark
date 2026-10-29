---- MODULE LargeStateSpace ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat

VARIABLES x, y, z

vars == <<x, y, z>>

Init ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ z \in 0..N

Next ==
    UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ z \in 0..N

Inv == TRUE

THEOREM Spec => [](TypeOK /\ Inv)
====