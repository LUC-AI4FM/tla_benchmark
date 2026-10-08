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

StateIsOne == x = 1
WorkDone == x = 2
WrapAround == x = 2 /\ x' = 0

Spec ==
    INIT Init
    /\ [] [][Next]_<<x>>
    /\ WF_next(Next)

(* TLC-specific check for named-state coverage *)
Assume TLCGet("NamedStateCoverage") =
    << "StateIsOne", 1,
       "WorkDone", 1,
       "WrapAround", 1 >>

=============================================================================