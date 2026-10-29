---------------------------- MODULE InvariantAsSpec ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

SetConst    == x' = 5
SetInRange  == \E v \in 0..3 : x' = v
SetOutRange == x' = 42
MapA        == x = 1 /\ x' = 2
MapB        == x = 2 /\ x' = 7

Next == \/ SetConst
        \/ SetInRange
        \/ SetOutRange
        \/ MapA
        \/ MapB

TypeOK == x \in 0..3

Inv == TypeOK /\ x = 0

Spec == Init /\ Inv /\ [][Next /\ Inv']_vars

=============================================================================