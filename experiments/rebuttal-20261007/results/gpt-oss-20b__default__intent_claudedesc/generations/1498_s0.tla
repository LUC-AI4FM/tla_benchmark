MODULE Toggle
EXTENDS Integers, TLC

VARIABLES b

Init == b = FALSE

A1 == /\ b' = ~b
A2 == /\ b' = ~b

Next == A1 \/ A2

Spec == Init /\ [] (Next)