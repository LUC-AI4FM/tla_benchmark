------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    \* No constants needed for this simple state machine

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x < 2
       /\ x' = x + 1
    \/ /\ x = 2
       /\ x' = 0

Spec == Init /\ [][Next]_<<x>>

StateIsOne == x = 1
AllWorkDone == x = 2
WrapAround == x = 2 /\ x' = 0

(*--algorithm check_coverage {
    variables covered = TLCGet("NamedStateCoverage")
}*)

TypeOK ==
    \/ StateIsOne
    \/ AllWorkDone
    \/ WrapAround

COVER == 
    /\ TypeOK
    /\ TLC_CARDINALITY({s \in TLC_GET("States") : s.StateIsOne}) = 1
    /\ TLC_CARDINALITY({s \in TLC_GET("States") : s.AllWorkDone}) = 1
    /\ TLC_CARDINALITY({s \in TLC_GET("States") : s.WrapAround}) = 1

=============================================================================