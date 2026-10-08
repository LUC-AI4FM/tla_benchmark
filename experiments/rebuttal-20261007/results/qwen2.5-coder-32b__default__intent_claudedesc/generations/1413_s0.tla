------------------------------- MODULE TemporalTautology -------------------------------
EXTENDS TLC, Integers

CONSTANTS 
    \* No constants needed for this trivial system

VARIABLES 
    x

Init == x = 0

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Invariant == <>TRUE => <>[]TRUE

THEOREM Spec => []Invariant
=============================================================================