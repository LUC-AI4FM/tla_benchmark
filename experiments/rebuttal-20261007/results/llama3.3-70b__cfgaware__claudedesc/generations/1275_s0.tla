---------------------------- MODULE SimpleSystemNeg ----------------------------
EXTENDS Integers

CONSTANT 

VARIABLE s

Init(var) == 
  \E x \in {0, 1} : var = x /\ x < 1

Spec == Init(s) /\ [][s' = s]_s

Inv == s < 1

=============================================================================