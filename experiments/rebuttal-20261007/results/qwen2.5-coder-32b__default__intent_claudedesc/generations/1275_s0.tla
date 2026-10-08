------------------------------- MODULE NonTrivialInit -------------------------------

EXTENDS Integers

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES x

Init == \/ x = 0
        /\ x < 1

Next == FALSE

Spec == Init /\ [][Next]_<<x>>

Inv == x < 1

THEOREM Spec => []Inv

=============================================================================