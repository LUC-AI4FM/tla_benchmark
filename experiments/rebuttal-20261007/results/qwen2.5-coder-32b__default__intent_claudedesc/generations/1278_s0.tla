------------------------------- MODULE EvenNumberRange -------------------------------
EXTENDS Integers

CONSTANTS 
    \* No constants needed for this specification

VARIABLES x

Init == x = 0

Next == \/ x' = x
        \/ /\ x' \in {0, 2, 4, 6, 8}
           /\ x' >= 0
           /\ x' <= 9

Spec == Init /\ [][Next]_<<x>>

=============================================================================