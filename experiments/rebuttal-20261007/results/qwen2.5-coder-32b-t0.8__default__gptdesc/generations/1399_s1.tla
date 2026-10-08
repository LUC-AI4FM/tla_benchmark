```tla
------------------------------- MODULE BooleanStateMachine -------------------------------
EXTENDS Naturals, TLC

CONSTANTS
    \* No constants needed for this specification

VARIABLES
    x

Init == x = TRUE

Next ==
    \/  /\ x' = ~x
        /\ UNCHANGED <<>>

Spec ==
    /\ Init
    /\ [][Next]_<<x>>
```