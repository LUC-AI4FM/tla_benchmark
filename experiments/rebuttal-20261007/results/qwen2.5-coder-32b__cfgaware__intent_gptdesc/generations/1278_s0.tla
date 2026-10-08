------------------------------- MODULE SimpleStateMachine ------------------------------

VARIABLES state

CONSTANTS Init, Spec, Next, StateOk

Init == state = 0

StateOk(s) == s \in {0, 2, 4, 6, 8}

Next ==
    /\ \/ state' = state
       \/ StateOk(state')
    /\ StateOk(state')

Spec ==
    /\ Init
    /\ [][Next]_<<state>>

=============================================================================