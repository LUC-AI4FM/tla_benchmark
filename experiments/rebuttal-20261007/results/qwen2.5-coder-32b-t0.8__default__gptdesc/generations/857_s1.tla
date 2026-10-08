---------------------------- MODULE PrisonerLightSwitch ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, INIT_KNOWN

VARIABLES lightState, prisonersVisited, counterPrisoner, announcedVictory

Init == /\ lightState \in {0, 1}
        /\ prisonersVisited = {}
        /\ counterPrisoner \in (1..N)
        /\ announcedVictory = FALSE
        /\ IF INIT_KNOWN THEN lightState = 0 ELSE TRUE

Next ==
    LET nextLightState == CASE /\ ~announcedVictory
                               /\ lightState = 0
                               /\ \/ (\E p \in prisonersVisited : p /= counterPrisoner)
                                  \/ (cardinality(prisonersVisited) < N - 1)
                        -> 1
                            [\* Toggle light on if not announced and off, and not all non-counter have visited or threshold is not met *)
                    [] /\ ~announcedVictory
                       /\ lightState = 1
                       /\ (\E p \in prisonersVisited : p = counterPrisoner)
                    -> 0
                        [\* Toggle light off if not announced and on, and counter has visited *)
                    [] TRUE -> lightState
                            [\* Otherwise, no change *)
        IN
        \/ /\ E (p \in 1..N) :
              \/ /\ ~announcedVictory
                 /\ p = counterPrisoner
                 /\ lightState = 1
                 -> /\ prisonersVisited' = prisonersVisited \cup {p}
                    /\ lightState' = nextLightState
                    /\ announcedVictory' = (cardinality(prisonersVisited \cup {p}) = IF INIT_KNOWN THEN N ELSE 2 * N - 1)
                    [\* Counter prisoner toggles light off and updates visited set, announces victory if threshold met *)
              \/ /\ ~announcedVictory
                 /\ p # counterPrisoner
                 -> /\ prisonersVisited' = prisonersVisited \cup {p}
                    /\ lightState' = nextLightState
                    [\* Non-counter prisoner visits, toggles light if off and not all have visited *)
              \/ /\ announcedVictory
                 -> /\ prisonersVisited' = prisonersVisited
                    /\ lightState' = lightState
                    [\* No change after victory announcement *)
        \/ /\ ~announcedVictory
           /\ lightState \in {0, 1}
           -> /\ prisonersVisited' = prisonersVisited
              /\ lightState' = lightState
              /\ announcedVictory' = FALSE
              [\* Warden selects a prisoner who does not change state if no one is selected *)

Spec ==
    /\ Init
    /\ [][Next]_<<lightState, prisonersVisited, announcedVictory>>
    /\ WF_next(Next)

Safety == /\ G~announcedVictory \/ prisonersVisited = {1..N}

Liveness == <>[](announcedVictory)

THEOREM Spec => []Safety

THEOREM Spec => Liveness
=============================================================================