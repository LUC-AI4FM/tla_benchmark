------------------------------- MODULE TemporalTautology -------------------------------

CONSTANTS
    \* No constants are needed for this specification

VARIABLES
    x

Init == x = 0

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

AlwaysTrue == <>TRUE => <>[]TRUE

=============================================================================