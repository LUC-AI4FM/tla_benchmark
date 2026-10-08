------------------------------- MODULE PrisonerLightSwitch -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N \* Number of prisoners

VARIABLES lightState, prisonerCount, prisonerStates, announcedVictory

Init == /\ lightState \in {0, 1} 
        /\ prisonerCount = 0
        /\ prisonerStates = [1..N -> FALSE]
        /\ announcedVictory = FALSE

Next == \/ /\ lightState = 0
             /\ \E p \in (1..N) \ {counter}: \neg prisonerStates[p] 
                /\ \/ prisonerStates[counter]
                   /\ prisonerCount' = 0
                   /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
                   /\ lightState' = 1
                  [] /\ \neg prisonerStates[counter]
                     /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
                     /\ lightState' = 0
             /\ announcedVictory' = announcedVictory
        \/ /\ lightState = 1
             /\ \E p \in (1..N) \ {counter}: prisonerStates[p]
                /\ \/ prisonerStates[counter]
                   /\ prisonerCount' = prisonerCount + 1
                   /\ prisonerStates' = [prisonerStates EXCEPT ![p] = FALSE]
                   /\ lightState' = 0
                  [] /\ \neg prisonerStates[counter]
                     /\ prisonerStates' = [prisonerStates EXCEPT ![p] = FALSE]
                     /\ lightState' = 1
             /\ announcedVictory' = announcedVictory
        \/ /\ lightState = 0
             /\ prisonerStates[counter]
             /\ prisonerCount >= 2 * N - 1
                /\ prisonerCount' = prisonerCount
                /\ prisonerStates' = prisonerStates
                /\ lightState' = 0
                /\ announcedVictory' = TRUE
        \/ /\ lightState = 1
             /\ prisonerStates[counter]
             /\ prisonerCount >= N - 1
                /\ prisonerCount' = prisonerCount
                /\ prisonerStates' = prisonerStates
                /\ lightState' = 1
                /\ announcedVictory' = TRUE

Spec == /\ Init
        /\ [][Next]_<<lightState, prisonerCount, prisonerStates, announcedVictory>>
        /\ WF_next(<<lightState, prisonerCount, prisonerStates, announcedVictory>>)

Safety == \A p \in 1..N: prisonerStates[p] => announcedVictory

Liveness == <>(announcedVictory)

THEOREM Spec => []<>Safety /\ []<>Liveness
=============================================================================