------------------------------ MODULE InstanceSpec ------------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

----------------------------- MODULE Component -----------------------------
EXTENDS Naturals

VARIABLE y

Range == 0..4

Init == y = 0

Next == y' = (y + 1) % 5

Spec == Init /\ [][Next]_y

CompTypeOK == y \in Range
=============================================================================