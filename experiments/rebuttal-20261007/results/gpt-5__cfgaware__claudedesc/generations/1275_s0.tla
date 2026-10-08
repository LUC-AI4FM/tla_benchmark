----------------------------- MODULE AssignInitNeg -----------------------------

EXTENDS Integers

VARIABLES s

Init(var) ==
  \E x \in {0, 1}:
    /\ var = x
    /\ x < 1

Next == UNCHANGED s

Spec == Init(s) /\ [][Next]_s

Inv == s < 1

=============================================================================