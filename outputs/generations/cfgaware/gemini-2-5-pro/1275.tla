---- MODULE solution ----
EXTENDS Integers

VARIABLES s

Init(var) == \E v \in 0..1 : (var = v) /\ (var < 1)

Inv == s < 1

Spec == Init(s) /\ [][UNCHANGED s]_s

=============================================================================