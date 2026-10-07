----------------------------- MODULE SingleVarTS -----------------------------
EXTENDS Naturals

CONSTANTS Max
ASSUME Max = 3

VARIABLES x

Init == x = 0

Next == IF x < Max THEN x' = x + 1 ELSE x' = x

Spec == Init /\ [][Next]_x
============================================================================