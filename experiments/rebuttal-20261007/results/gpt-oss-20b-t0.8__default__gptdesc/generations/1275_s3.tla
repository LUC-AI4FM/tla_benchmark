------------------------------ MODULE InitPattern ------------------------------
EXTENDS Integers, TemporalOperators
VARIABLE s

Init == (s \in 0 .. 1) /\ (s < 1)

Next == UNCHANGED s

Spec == Init /\ [] (Next)

Inv == s < 1
=============================================================================