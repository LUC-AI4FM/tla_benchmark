------------------------------- MODULE NegTest -------------------------------
EXTENDS Integers

CONSTANTS var

VARIABLES s

Init == \E x \in {0, 1} : s = x /\ x < 1

Next == s' = s

Spec == Init /\ [][Next]_<<s>>

Inv == s < 1
=============================================================================