------------------------------ MODULE PrisonerLightSwitch ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of prisoners

VARIABLES light, counterVisits, prisonerStates, announcedVictory

vars == <<light, counterVisits, prisonerStates, announcedVictory>>

Init == /\ light \in {0, 1}
        /\ counterVisits = 0
        /\ prisonerStates = [p \in 1..N -> FALSE]
        /\ announcedVictory = FALSE

Next == \/ /\ light = 0
            /\ \/ /\ \E p \in 1..N \ {1} : prisonerStates[p] & ~announcedVictory
                 /\ light' = 1
                 /\ counterVisits' = IF p = 1 THEN counterVisits + 1 ELSE counterVisits
                 /\ prisonerStates' = [prisonerStates EXCEPT ![p] = FALSE]
            \/ /\ \A p \in 1..N : ~prisonerStates[p] \/ announcedVictory
                 /\ light' = light
                 /\ counterVisits' = counterVisits
                 /\ prisonerStates' = prisonerStates
        /\ /\ light = 1
            /\ \/ /\ \E p \in 1..N \ {1} : ~prisonerStates[p]
                 /\ light' = 0
                 /\ counterVisits' = counterVisits
                 /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
            \/ /\ \A p \in 1..N : prisonerStates[p]
                 /\ light' = 1
                 /\ IF announcedVictory THEN
                    /\ counterVisits' = counterVisits
                    /\ prisonerStates' = prisonerStates
                  ELSE
                    /\ (counterVisits' = IF 2 * N - 1 <= counterVisits + 1 THEN counterVisits + 1 ELSE counterVisits)
                    /\ prisonerStates' = [prisonerStates EXCEPT ![1] = FALSE]
                 /\ announcedVictory' = IF 2 * N - 1 <= counterVisits + 1 THEN TRUE ELSE FALSE
        \/ /\ light \in {0, 1}
           /\ \E p \in 1..N : ~prisonerStates[p] & p # 1
           /\ light' = light
           /\ counterVisits' = counterVisits
           /\ prisonerStates' = [prisonerStates EXCEPT ![p] = TRUE]
           /\ announcedVictory' = announcedVictory

Spec == /\ Init
        /\ SF_<<1..N>>
        /\ [][Next]_<<light, counterVisits, prisonerStates, announcedVictory>>
        /\ WF_<<1..N>>[Next]

AnnouncementImpliesAllVisited ==
    \/ ~announcedVictory
    \/ \A p \in 1..N : prisonerStates[p]

THEOREM Spec => []AnnouncementImpliesAllVisited

=============================================================================