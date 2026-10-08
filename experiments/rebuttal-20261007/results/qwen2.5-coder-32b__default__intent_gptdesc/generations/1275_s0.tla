------------------------------- MODULE SimpleStateVar -------------------------------
EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this simple specification

VARIABLES 
    value

Init == \/ value = 0

Next == TRUE

Spec == /\ Init
        /\ [][Next]_<<value>>
        /\ WF_next(<<value>>)

Invariants ==
    /\ value < 1

Liveness ==
    <>[](value' = value)

=============================================================================