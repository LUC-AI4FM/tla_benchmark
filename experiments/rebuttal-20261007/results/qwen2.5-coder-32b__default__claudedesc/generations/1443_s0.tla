------------------------------- MODULE TestPossibilityTracking -------------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxCount

VARIABLES x

Init == x = 0

Next == \/ /\ x < 2
            /\ x' = x + 1
         \/ /\ x = 2
            /\ x' = 0

Spec ==
    Init /\ [][Next]_<<x>>

AllDone == x = 2
AtOne == x = 1
WrapAround == x = 2 /\ x' = 0

PossibleCounts ==
    LET counts == TLCGet("all:named")
    IN /\ counts["AllDone"] = 1
       /\ counts["AtOne"] = 1
       /\ counts["WrapAround"] = 1

=============================================================================