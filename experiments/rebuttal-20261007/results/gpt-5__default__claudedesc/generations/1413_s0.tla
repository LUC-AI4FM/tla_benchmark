----------------------------- MODULE Github790 -----------------------------
EXTENDS Integers

VARIABLES a

Init == a = 0

Next == a' = a

Spec == Init /\ [][Next]_a

TypeOK == a \in Int
AlwaysZero == a = 0
SafetyInv == TypeOK /\ AlwaysZero

AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM Spec => []SafetyInv
THEOREM AlwaysTrue
============================================================================