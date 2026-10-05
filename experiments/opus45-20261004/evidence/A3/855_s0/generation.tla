---------------------------- MODULE PrisonersAndSwitches ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 2

Prisoners == 1..N

Counter == 1

NonCounters == 2..N

VARIABLES
    switchA,
    switchB,
    count,
    timesFlippedA,
    declared,
    inRoom

vars == <<switchA, switchB, count, timesFlippedA, declared, inRoom>>

TypeOK ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count \in 0..(2 * (N - 1))
    /\ timesFlippedA \in [NonCounters -> 0..2]
    /\ declared \in BOOLEAN
    /\ inRoom \in Prisoners \cup {0}

Init ==
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ count = 0
    /\ timesFlippedA = [p \in NonCounters |-> 0]
    /\ declared = FALSE
    /\ inRoom = 0

CounterAction ==
    /\ inRoom = Counter
    /\ ~declared
    /\ IF switchA = TRUE
       THEN /\ switchA' = FALSE
            /\ count' = count + 1
            /\ IF count + 1 = 2 * (N - 1)
               THEN declared' = TRUE
               ELSE declared' = declared
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ count' = count
            /\ declared' = declared
    /\ UNCHANGED timesFlippedA
    /\ inRoom' = 0

NonCounterAction(p) ==
    /\ inRoom = p
    /\ p \in NonCounters
    /\ ~declared
    /\ IF switchA = FALSE /\ timesFlippedA[p] < 2
       THEN /\ switchA' = TRUE
            /\ timesFlippedA' = [timesFlippedA EXCEPT ![p] = @ + 1]
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ timesFlippedA' = timesFlippedA
    /\ UNCHANGED <<count, declared>>
    /\ inRoom' = 0

SelectPrisoner(p) ==
    /\ inRoom = 0
    /\ ~declared
    /\ inRoom' = p
    /\ UNCHANGED <<switchA, switchB, count, timesFlippedA, declared>>

Terminated ==
    /\ declared
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Prisoners : SelectPrisoner(p)
    \/ CounterAction
    \/ \E p \in NonCounters : NonCounterAction(p)
    \/ Terminated

CounterFairness == WF_vars(CounterAction)

NonCounterFairness == \A p \in NonCounters : WF_vars(NonCounterAction(p))

SelectionFairness == \A p \in Prisoners : WF_vars(SelectPrisoner(p))

Fairness == CounterFairness /\ NonCounterFairness /\ SelectionFairness

Spec == Init /\ [][Next]_vars /\ Fairness

visited == {p \in NonCounters : timesFlippedA[p] > 0} \cup 
           (IF count > 0 THEN {Counter} ELSE {})

Safety == declared => (visited = Prisoners)

Liveness == <>declared

===================================================================================