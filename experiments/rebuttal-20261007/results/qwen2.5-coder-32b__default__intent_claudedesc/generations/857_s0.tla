------------------------------- MODULE PrisonerLampPuzzle -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, KNOWN_OFF \* KNOWN_OFF is a boolean flag indicating if the initial state of the lamp is known to be off

VARIABLES lampState, prisonerCount, visitedPrisoners

Init == /\ lampState = IF KNOWN_OFF THEN FALSE ELSE BOOLEAN
        /\ prisonerCount = 0
        /\ visitedPrisoners = {}

Next ==
    LET chosenPrisoner \in (1..N) IN
    \/ /\ lampState = TRUE
       /\ prisonerCount < (IF KNOWN_OFF THEN N ELSE 2*N - 1)
       /\ chosenPrisoner = 1
       /\ prisonerCount' = prisonerCount + 1
       /\ lampState' = FALSE
       /\ visitedPrisoners' = IF chosenPrisoner \notin visitedPrisoners THEN visitedPrisoners \cup {chosenPrisoner} ELSE visitedPrisoners
    \/ /\ lampState = FALSE
       /\ (chosenPrisoner > 1)
       /\ prisonerCount' = prisonerCount
       /\ lampState' = IF chosenPrisoner \notin visitedPrisoners THEN TRUE ELSE lampState
       /\ visitedPrisoners' = IF chosenPrisoner \notin visitedPrisoners THEN visitedPrisoners \cup {chosenPrisoner} ELSE visitedPrisoners

Spec ==
    /\ Init
    /\ [][Next]_<<lampState, prisonerCount, visitedPrisoners>>
    /\ WF_<<1..N>>(Next)

Safety == [](prisonerCount < (IF KNOWN_OFF THEN N ELSE 2*N - 1) \/ (Cardinality(visitedPrisoners) = N))

Liveness ==
    <>(/\ prisonerCount >= (IF KNOWN_OFF THEN N ELSE 2*N - 1)
        /\ Cardinality(visitedPrisoners) = N)

THEOREM Spec => []Safety
THEOREM Spec => <>Liveness

=============================================================================