---------------------------- MODULE prisoners ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Prisoner, p2, p3

VARIABLES switchA, switchB, count, declared, visited, numFlips, turn

vars == <<switchA, switchB, count, declared, visited, numFlips, turn>>

Counter == CHOOSE p \in Prisoner : TRUE

NonCounters == Prisoner \ {Counter}

N == Cardinality(Prisoner)

TypeOK ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count \in 0..(2 * N)
    /\ declared \in BOOLEAN
    /\ visited \subseteq Prisoner
    /\ numFlips \in [NonCounters -> 0..2]
    /\ turn \in Prisoner

Init ==
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ count = 0
    /\ declared = FALSE
    /\ visited = {}
    /\ numFlips = [p \in NonCounters |-> 0]
    /\ turn \in Prisoner

CounterAction ==
    /\ turn = Counter
    /\ visited' = visited \cup {Counter}
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
    /\ numFlips' = numFlips
    /\ turn' \in Prisoner

NonCounterAction(p) ==
    /\ turn = p
    /\ p \in NonCounters
    /\ visited' = visited \cup {p}
    /\ IF switchA = FALSE /\ numFlips[p] < 2
       THEN /\ switchA' = TRUE
            /\ numFlips' = [numFlips EXCEPT ![p] = numFlips[p] + 1]
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ numFlips' = numFlips
    /\ count' = count
    /\ declared' = declared
    /\ turn' \in Prisoner

Next ==
    \/ CounterAction
    \/ \E p \in NonCounters : NonCounterAction(p)

CounterFairness == WF_vars(CounterAction)

NonCounterFairness == \A p \in NonCounters : WF_vars(NonCounterAction(p))

Fairness == CounterFairness /\ NonCounterFairness

Spec == Init /\ [][Next]_vars /\ Fairness

CountInvariant == count <= 2 * (N - 1)

Safety == declared => (visited = Prisoner)

Liveness == <>(declared)

==========================================================================