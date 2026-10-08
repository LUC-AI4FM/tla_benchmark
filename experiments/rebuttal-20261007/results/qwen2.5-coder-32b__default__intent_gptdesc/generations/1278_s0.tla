------------------------------- MODULE SimpleStateMachine -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    \* No constants needed for this simple state machine

VARIABLES 
    state

Init == state = 0

Next ==
    /\ \/ state' = state
       \/ (state' \in {0, 2, 4, 6, 8})
    /\ state' \in 0..9
    /\ state' % 2 = 0

Spec ==
    /\ Init
    /\ [][Next]_<<state>>

SafetyInvariant ==
    /\ state \in 0..9
    /\ state % 2 = 0

=============================================================================