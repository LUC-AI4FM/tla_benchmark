------------------------------- MODULE PossibilityTest -------------------------------

CONSTANTS
    \* No additional constants are needed for this specification

VARIABLES x

Init == x = 0

Next ==
    /\ \/ x' = (x + 1) % 3
    /\ UNCHANGED << >>

Spec ==
    Init /\ [][Next]_<<x>>

AllDone == x = 2
AtOne == x = 1
WrapAround == x = 2 /\ x' = 0

PossibleCounts ==
    LET counts == TLCGet("all:named")
    IN
        /\ counts["AllDone"] = 1
        /\ counts["AtOne"] = 1
        /\ counts["WrapAround"] = 1

=============================================================================