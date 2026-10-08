------------------------------- MODULE PrisonerLightSwitch -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of prisoners

VARIABLES lightState, counterVisits, prisonerStates, announcedVictory

Init == 
  /\ lightState \in {0, 1} \* 0 = off, 1 = on
  /\ counterVisits = 0
  /\ prisonerStates = [p \in 1..N -> FALSE] \* TRUE if prisoner p has visited the cell
  /\ announcedVictory = FALSE

Next == 
  \/ /\ lightState = 0
     /\ \E p \in 1..N \ (prisonerStates[p] = FALSE)
     /\ \/ /\ p = 1 \* Counter prisoner
            /\ lightState' = 1
            /\ counterVisits' = counterVisits + 1
            /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
            /\ announcedVictory' = IF (IF lightState = 0 THEN N ELSE 2*N - 1) <= counterVisits + 1 THEN TRUE ELSE FALSE
        \/ /\ p \notin {1} \* Non-counter prisoner
           /\ lightState' = 1
           /\ counterVisits' = counterVisits
           /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
           /\ announcedVictory' = announcedVictory
  \/ /\ lightState = 1
     /\ \E p \in 1..N \ (prisonerStates[p] = FALSE)
     /\ \/ /\ p = 1 \* Counter prisoner
            /\ lightState' = 0
            /\ counterVisits' = counterVisits
            /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
            /\ announcedVictory' = announcedVictory
        \/ /\ p \notin {1} \* Non-counter prisoner
           /\ lightState' = lightState
           /\ counterVisits' = counterVisits
           /\ prisonerStates' = prisonerStates
           /\ announcedVictory' = announcedVictory

Spec == 
  /\ Init
  /\ [][Next]_<<lightState, counterVisits, prisonerStates, announcedVictory>>
  /\ WF_<<lightState, counterVisits, prisonerStates, announcedVictory>> (Next)

SafetyInvariant ==
  \/ \A p \in 1..N : prisonerStates[p]
     /\ announcedVictory

LivenessProperty ==
  <>[](announcedVictory)

THEOREM Spec => []<>(SafetyInvariant)
THEOREM Spec => LivenessProperty
=============================================================================