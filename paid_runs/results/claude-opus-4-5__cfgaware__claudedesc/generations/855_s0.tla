---------------------------- MODULE prisoners ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Prisoner, p2, p3

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

Counter == CHOOSE p \in Prisoner : TRUE

NonCounters == Prisoner \ {Counter}

TypeOK ==
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched \in [NonCounters -> 0..2]
    /\ count \in 0..(2 * (Cardinality(Prisoner) - 1))

Done == count = 2 * (Cardinality(Prisoner) - 1)

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

TotalSwitched == 
    LET S == {timesSwitched[p] : p \in NonCounters}
    IN LET Sum[T \in SUBSET NonCounters] ==
           IF T = {} THEN 0
           ELSE LET x == CHOOSE x \in T : TRUE
                IN timesSwitched[x] + Sum[T \ {x}]
       IN Sum[NonCounters]

CountInvariant ==
    /\ count <= TotalSwitched
    /\ IF switchAUp 
       THEN count + 1 <= TotalSwitched
       ELSE count <= TotalSwitched

Safety ==
    Done => \A p \in NonCounters : timesSwitched[p] >= 1

Liveness == <>Done

==========================================================================