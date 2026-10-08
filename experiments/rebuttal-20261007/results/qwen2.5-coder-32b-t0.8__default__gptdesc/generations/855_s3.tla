------------------------------- MODULE PrisonersAndSwitches -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Prisons, Counter

VARIABLES switchA, switchB, visits

Init == /\ switchA = FALSE
        /\ switchB = FALSE
        /\ visits = {}

Next ==
    LET prisoner = CHOOSE p \in Prisons : TRUE
        IN \/ /\ prisoner = Counter
               /\ \/ IF switchA THEN visits' = visits \cup {prisoner}
                  ELSE visits' = visits
               /\ IF switchA THEN switchA' = FALSE
                  ELSE switchA' = switchA
               /\ switchB' = switchB
           \/ /\ prisoner # Counter
               /\ visits' = visits \cup {prisoner}
               /\ switchA' = IF switchA = FALSE /\ (prisoner \notin visits) 
                              THEN TRUE 
                              ELSE switchA
               /\ switchB' = ~switchB

Spec ==
    /\ Init
    /\ [][Next]_<<switchA, switchB, visits>>
    /\ WF_(<<Counter>>)
    /\ SF_\forall(p \in Prisons \ {Counter} | <<p>>)

Completion == visits = Prisons

TypeInvariant == 
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ visits \subseteq Prisons

Safety == TypeInvariant /\ [](Completion -> []Completion)

Liveness == <>(Completion)

THEOREM Spec => []Safety

THEOREM Spec => Liveness
=============================================================================