---- MODULE TerminationDetection ----

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node

VARIABLES state, detected

Init == /\ state \in [Node -> BOOLEAN]
        /\ detected = FALSE

Next ==
    \/ \/ /\ EXISTING n \in Node : state[n] 
           /\ \/ /\ state' = [state EXCEPT ![n] = FALSE]
              \/ /\ CHOOSE m \in Node \ {n} : TRUE
                 /\ state' = [state EXCEPT ![m] = TRUE]
        \/ /\ detected = FALSE
           /\ ALL_NODES_INACTIVE(state)
           /\ detected' = TRUE
           /\ state' = state
        \/ /\ detected'
           /\ state' = state

ALL_NODES_INACTIVE(state) == \A n \in Node : ~state[n]

Spec ==
    /\ Init
    /\ [][Next]_<<state, detected>>
    /\ WF_next(<<state, detected>>)

TerminationDetected ==
    <>(detected)

Quiescence ==
    <>[]<>(ALL_NODES_INACTIVE(state))

Correctness ==
    [](detected => ALL_NODES_INACTIVE(state))

====