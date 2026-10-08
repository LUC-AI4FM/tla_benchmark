```tla
MODULE PrisonerLightSwitch

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N \* Number of prisoners

VARIABLES lightState, counterVisits, prisonersVisited

Init == /\ lightState = FALSE 
        /\ counterVisits = 0 
        /\ prisonersVisited = {}

Next == \/ /\ ~(\E p \in (1..N) : prisonersVisited[p]) 
            /\ lightState = FALSE
            /\ CHOOSE p \in (1..N) : ~prisonersVisited[p] -> 
                (\* Non-counter prisoner turns on the light *)
                /\ lightState' = TRUE 
                /\ counterVisits' = counterVisits
                /\ prisonersVisited' = prisonersVisited
        \/ /\ lightState = TRUE 
            /\ CHOOSE p \in (1..N) : p # 1 -> 
                (\* Non-counter prisoner turns off the light *)
                /\ lightState' = FALSE 
                /\ counterVisits' = IF prisonersVisited[p] THEN counterVisits + 1 ELSE counterVisits
                /\ prisonersVisited' = prisonersVisited \cup {p}
        \/ /\ lightState = TRUE 
            /\ CHOOSE p \in (1..N) : p = 1 -> 
                (\* Counter prisoner counts and resets if threshold reached *)
                /\ IF counterVisits >= 2*N - 1 THEN
                    /\ lightState' = FALSE 
                    /\ counterVisits' = 0 
                    /\ prisonersVisited' = {}
                ELSE
                    /\ lightState' = TRUE 
                    /\ counterVisits' = counterVisits
                    /\ prisonersVisited' = prisonersVisited

Spec == Init /\ [][Next]_<<lightState, counterVisits, prisonersVisited>>

AnnouncementImpliesAllVisited ==
    /\ (\E p \in (1..N) : prisonersVisited[p])
    -> /\ lightState = FALSE 
       /\ counterVisits >= 2*N - 1
       /\ prisonersVisited = {1} \cup (1..N)

WF == WF_<<lightState, counterVisits, prisonersVisited>>_Next

CompleteSpec == Spec /\ WF /\ AnnouncementImpliesAllVisited
```