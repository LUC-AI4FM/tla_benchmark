------------------------------- MODULE PrisonerPuzzle -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Light_Unknown

VARIABLES count, victoryAnnounced, signalled, lampState, visits

Init == /\ count = 1
        /\ victoryAnnounced = FALSE
        /\ signalled \in [Prisoner -> {0, 1}]
        /\ lampState \in BOOLEAN
        /\ visits = {}
        /\ IF Light_Unknown THEN lampState \in {TRUE, FALSE}
           ELSE lampState = FALSE

Next == \/ /\ wardenSelects \in Prisoner
            /\ visits' = visits \cup {wardenSelects}
            /\ count' = count
            /\ victoryAnnounced' = victoryAnnounced
            /\ signalled' = [p \in Prisoner |-> IF p = wardenSelects & lampState = FALSE THEN 
                                                            IF Light_Unknown & signalled[p] < 2 THEN signalled[p] + 1
                                                            ELSE IF ~Light_Unknown & signalled[p] = 0 THEN 1
                                                            ELSE signalled[p]
                                                        ELSE signalled[p]]
            /\ lampState' = IF wardenSelects \in Prisoner \ {CHOOSE p \in Prisoner : p # CHOOSE c \in Prisoner : TRUE} 
                             /\ lampState = FALSE 
                             /\ (Light_Unknown => signalled[wardenSelects] < 2)
                             /\ (~Light_Unknown => signalled[wardenSelects] = 0) 
                           THEN TRUE
                           ELSE lampState
        \/ /\ wardenSelects \in Prisoner
            /\ visits' = visits \cup {wardenSelects}
            /\ count' = IF wardenSelects = CHOOSE p \in Prisoner : TRUE & lampState = TRUE THEN count + 1 ELSE count
            /\ victoryAnnounced' = IF (count' = CARD(Prisoner) \/ (Light_Unknown & count' = 2 * CARD(Prisoner) - 1)) 
                                   /\ visits = Prisoner 
                                 THEN TRUE 
                                 ELSE victoryAnnounced
            /\ signalled' = signalled
            /\ lampState' = IF wardenSelects = CHOOSE p \in Prisoner : TRUE & lampState = TRUE THEN FALSE ELSE lampState

Spec == Init /\ [][Next]_<<wardenSelects>>

TypeOK == /\ count \in 1..2 * CARD(Prisoner)
          /\ victoryAnnounced \in BOOLEAN
          /\ signalled \in [Prisoner -> {0, 1}]
          /\ lampState \in BOOLEAN
          /\ visits \subseteq Prisoner

VictoryOK == \/ ~victoryAnnounced
             \/ (victoryAnnounced /\ visits = Prisoner)

Terminating == <>[](victoryAnnounced)

WF == WF_<<wardenSelects>>_

THEOREM Spec => []TypeOK /\ []VictoryOK /\ Terminating /\ WF
=============================================================================