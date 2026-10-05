---------------------------- MODULE Prisoners ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N > 1

Prisoners == 1..N

Counter == 1

NonCounters == 2..N

VARIABLES
    switchA,
    switchB,
    count,
    flipped,
    declared,
    freed,
    turn

vars == <<switchA, switchB, count, flipped, declared, freed, turn>>

TypeOK ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count \in 0..(N-1)
    /\ flipped \in SUBSET NonCounters
    /\ declared \in BOOLEAN
    /\ freed \in BOOLEAN
    /\ turn \in Prisoners \cup {0}

Init ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count = 0
    /\ flipped = {}
    /\ declared = FALSE
    /\ freed = FALSE
    /\ turn = 0

SelectPrisoner(p) ==
    /\ turn = 0
    /\ ~declared
    /\ turn' = p
    /\ UNCHANGED <<switchA, switchB, count, flipped, declared, freed>>

CounterAction ==
    /\ turn = Counter
    /\ ~declared
    /\ \/ /\ switchA = TRUE
          /\ count' = count + 1
          /\ switchA' = FALSE
          /\ UNCHANGED switchB
       \/ /\ switchA = FALSE
          /\ switchB' = ~switchB
          /\ UNCHANGED <<switchA, count>>
    /\ turn' = 0
    /\ UNCHANGED <<flipped, declared, freed>>

NonCounterAction(p) ==
    /\ turn = p
    /\ p \in NonCounters
    /\ ~declared
    /\ \/ /\ p \notin flipped
          /\ switchA = FALSE
          /\ switchA' = TRUE
          /\ flipped' = flipped \cup {p}
          /\ UNCHANGED switchB
       \/ /\ p \in flipped
          /\ switchB' = ~switchB
          /\ UNCHANGED <<switchA, flipped>>
       \/ /\ p \notin flipped
          /\ switchA = TRUE
          /\ switchB' = ~switchB
          /\ UNCHANGED <<switchA, flipped>>
    /\ turn' = 0
    /\ UNCHANGED <<count, declared, freed>>

Declare ==
    /\ turn = Counter
    /\ ~declared
    /\ count >= N - 1
    /\ declared' = TRUE
    /\ freed' = (flipped = NonCounters)
    /\ turn' = 0
    /\ UNCHANGED <<switchA, switchB, count, flipped>>

Terminated ==
    /\ declared
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Prisoners : SelectPrisoner(p)
    \/ CounterAction
    \/ \E p \in NonCounters : NonCounterAction(p)
    \/ Declare
    \/ Terminated

Fairness ==
    /\ \A p \in Prisoners : WF_vars(SelectPrisoner(p))
    /\ WF_vars(CounterAction)
    /\ \A p \in NonCounters : WF_vars(NonCounterAction(p))
    /\ WF_vars(Declare)

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == declared => (flipped = NonCounters)

Liveness == <>(declared /\ freed)

==========================================================================