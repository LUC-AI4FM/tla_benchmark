---------------------------- MODULE Specification ----------------------------

EXTENDS Integers

VARIABLES s

Init(var) == \E v \in 0..1 : var = v /\ var < 1

Next == UNCHANGED s

Spec == Init(s) /\ [][UNCHANGED s]_s

Inv == s < 1

=============================================================================