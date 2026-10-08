---------------------------- MODULE AssignmentInitNeg ----------------------------
EXTENDS Integers

VARIABLE s

Init(var) == \E v \in {0, 1} : var = v /\ v < 1

Spec == Init(s) /\ [][FALSE]_s

Inv == s < 1

=============================================================================