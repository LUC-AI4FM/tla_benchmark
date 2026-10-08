---- MODULE PrisonersAndSwitches ----

CONSTANTS Prisoner, p2, p3

VARIABLES switchAUp, switchBUp, timesSwitched, count

ASSUME Cardinality(Prisoner) = 4 /\ p2 \in Prisoner /\ p3 \in Prisoner /\ p2 # p3

Counter == CHOOSE p \in Prisoner : TRUE

Init == /\ switchAUp \in {TRUE, FALSE}
        /\ switchBUp \in {TRUE, FALSE}
        /\ timesSwitched \in [Prisoner \ Counter -> {0, 1, 2}]
        /\ count = 0

Next ==
    LET p == CHOOSE pr \in Prisoner : TRUE
    IN \/ /\ p = Counter
           /\ (switchAUp => /\ switchAUp' = FALSE
                              /\ count' = count + 1
                              /\ UNCHANGED <<switchBUp, timesSwitched>>)
           /\ (NOT switchAUp => /\ switchBUp' = NOT switchBUp
                                /\ count' = count
                                /\ UNCHANGED <<switchAUp, timesSwitched>>)
       \/ /\ p # Counter
          /\ (timesSwitched[p] < 2) => /\ switchAUp' = TRUE
                                         /\ timesSwitched' = [timesSwitched EXCEPT ![p] = timesSwitched[p] + 1]
                                         /\ UNCHANGED <<switchBUp, count>>
          /\ (timesSwitched[p] >= 2) => /\ switchBUp' = NOT switchBUp
                                         /\ timesSwitched' = timesSwitched
                                         /\ UNCHANGED <<switchAUp, count>>

Spec == Init /\ [][Next]_<<switchAUp, switchBUp, timesSwitched, count>>

TypeOK ==
    /\ switchAUp \in {TRUE, FALSE}
    /\ switchBUp \in {TRUE, FALSE}
    /\ timesSwitched \in [Prisoner \ Counter -> {0, 1, 2}]
    /\ count \in 0..(2 * Cardinality(Prisoner) - 1)

CountInvariant ==
    LET totalAFlips == SUM p \in Prisoner \ Counter |-> timesSwitched[p]
    IN \/ switchAUp => count = totalAFlips
       /\ NOT switchAUp => count = totalAFlips + 1

Safety ==
    LET allVisited == \A p \in Prisoner \ Counter : timesSwitched[p] >= 1
    IN [](count < 2 * Cardinality(Prisoner) - 1 \/ (allVisited /\ Done))

Liveness ==
    LET allVisited == \A p \in Prisoner \ Counter : timesSwitched[p] >= 1
    IN <>[](Done)

Done == count = 2 * Cardinality(Prisoner) - 1

WFSpec == WF_vars(Next, <<switchAUp, switchBUp, timesSwitched, count>>)

====