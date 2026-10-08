---- MODULE PrisonersAndSwitches ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    PRISONERS,  \* Set of all prisoners
    COUNTER     \* The designated prisoner who acts as a counter

VARIABLES
    switchA,    \* State of switch A (BOOLEAN)
    switchB,    \* State of switch B (BOOLEAN)
    count       \* Count of times the counter has seen switch A up

Init == /\ switchA = FALSE
        /\ switchB = FALSE
        /\ count = 0

Next ==
    \/ \/ \E p \in PRISONERS \ {COUNTER} :
            \/ /\ switchA
               /\ switchB = TRUE
               /\ switchB' = FALSE
            \/ /\ ~switchA
               /\ (switchB = TRUE \/ switchB = FALSE)
               /\ switchB' = ~switchB
        \/ /\ p = COUNTER
           /\ switchA
           /\ count < CARDINALITY(PRISONERS) - 1
           /\ switchA' = FALSE
           /\ count' = count + 1
           /\ switchB' = switchB
        \/ /\ p = COUNTER
           /\ ~switchA
           /\ (switchB = TRUE \/ switchB = FALSE)
           /\ switchA' = switchA
           /\ count' = count
           /\ switchB' = switchB

Spec ==
    \* Initial state and next-state relation
    /\ Init
    /\ [][Next]_<<switchA, switchB, count>>
    /\ WF_<<switchA, switchB, count>>(Next)

\* Safety property: When the protocol declares completion, every prisoner has visited the room.
Safety ==
    \/ count < CARDINALITY(PRISONERS) - 1
    \/ count = CARDINALITY(PRISONERS) - 1

\* Liveness property: The declaration condition is eventually reached.
Liveness ==
    <>[](count = CARDINALITY(PRISONERS) - 1)

====