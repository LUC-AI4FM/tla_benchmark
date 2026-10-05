------------------------------ MODULE PrisonersAndSwitches ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME Counter \in Prisoner
ASSUME Cardinality(Prisoner) >= 2

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

NonCounters == Prisoner \ {Counter}

MaxCount == 2 * (Cardinality(Prisoner) - 1)

TypeOK ==
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched \in [NonCounters -> 0..2]
    /\ count \in 0..MaxCount

Done == count = MaxCount

Init ==
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched = [p \in NonCounters |-> 0]
    /\ count = 0

CounterAction ==
    /\ ~Done
    /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ switchBUp' = switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ switchAUp' = switchAUp
            /\ count' = count
    /\ UNCHANGED timesSwitched

NonCounterAction(p) ==
    /\ p \in NonCounters
    /\ ~Done
    /\ IF ~switchAUp /\ timesSwitched[p] < 2
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![p] = @ + 1]
            /\ switchBUp' = switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ switchAUp' = switchAUp
            /\ timesSwitched' = timesSwitched
    /\ UNCHANGED count

Next ==
    \/ CounterAction
    \/ \E p \in NonCounters : NonCounterAction(p)

Fairness ==
    /\ WF_vars(CounterAction)
    /\ \A p \in NonCounters : WF_vars(NonCounterAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

TotalTimesSwitched == 
    LET Sum[S \in SUBSET NonCounters] ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE p \in S : TRUE
             IN timesSwitched[p] + Sum[S \ {p}]
    IN Sum[NonCounters]

CountInvariant ==
    count = TotalTimesSwitched - IF switchAUp THEN 1 ELSE 0

AllVisited == \A p \in NonCounters : timesSwitched[p] >= 1

Safety == Done => AllVisited

Liveness == <>Done

=============================================================================