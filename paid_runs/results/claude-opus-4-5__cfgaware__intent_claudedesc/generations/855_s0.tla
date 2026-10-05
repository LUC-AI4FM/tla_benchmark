---------------------------- MODULE prisoners ----------------------------

EXTENDS Integers, FiniteSets

CONSTANT Prisoner, p2, p3

VARIABLES switchA, switchB, counter, flipped, declared, freed

vars == <<switchA, switchB, counter, flipped, declared, freed>>

NumPrisoners == Cardinality(Prisoner)

NonCounters == Prisoner \ {p2}

Init ==
    /\ switchA \in {TRUE, FALSE}
    /\ switchB \in {TRUE, FALSE}
    /\ counter = 0
    /\ flipped = {}
    /\ declared = FALSE
    /\ freed = FALSE

CounterVisit ==
    /\ ~declared
    /\ \E p \in {p2}:
        /\ IF switchA = TRUE
           THEN /\ switchA' = FALSE
                /\ counter' = counter + 1
                /\ switchB' = switchB
           ELSE /\ switchB' = ~switchB
                /\ switchA' = switchA
                /\ counter' = counter
        /\ flipped' = flipped
        /\ IF counter' >= 2 * (NumPrisoners - 1)
           THEN /\ declared' = TRUE
                /\ freed' = TRUE
           ELSE /\ declared' = FALSE
                /\ freed' = FALSE

NonCounterVisit(p) ==
    /\ ~declared
    /\ p \in NonCounters
    /\ IF p \notin flipped /\ switchA = FALSE
       THEN /\ switchA' = TRUE
            /\ flipped' = flipped \union {p}
            /\ switchB' = switchB
       ELSE IF p \in flipped /\ switchA = FALSE
            THEN /\ switchA' = TRUE
                 /\ flipped' = flipped
                 /\ switchB' = switchB
            ELSE /\ switchB' = ~switchB
                 /\ switchA' = switchA
                 /\ flipped' = flipped
    /\ counter' = counter
    /\ declared' = FALSE
    /\ freed' = FALSE

NonCounterVisitOnce(p) ==
    /\ ~declared
    /\ p \in NonCounters
    /\ IF p \notin flipped /\ switchA = FALSE
       THEN /\ switchA' = TRUE
            /\ flipped' = flipped \union {p}
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ flipped' = flipped
    /\ counter' = counter
    /\ declared' = FALSE
    /\ freed' = FALSE

CounterAction ==
    /\ ~declared
    /\ IF switchA = TRUE
       THEN /\ switchA' = FALSE
            /\ counter' = counter + 1
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ counter' = counter
    /\ flipped' = flipped
    /\ IF counter' >= 2 * (NumPrisoners - 1)
       THEN /\ declared' = TRUE
            /\ freed' = TRUE
       ELSE /\ declared' = FALSE
            /\ freed' = FALSE

Next ==
    \/ CounterAction
    \/ \E p \in NonCounters: NonCounterVisitOnce(p)

Fairness ==
    /\ WF_vars(CounterAction)
    /\ \A p \in NonCounters: WF_vars(NonCounterVisitOnce(p))

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK ==
    /\ switchA \in {TRUE, FALSE}
    /\ switchB \in {TRUE, FALSE}
    /\ counter \in 0..2*NumPrisoners
    /\ flipped \subseteq NonCounters
    /\ declared \in {TRUE, FALSE}
    /\ freed \in {TRUE, FALSE}

CountInvariant ==
    counter <= 2 * Cardinality(flipped) + 2

Safety ==
    declared => (NonCounters \subseteq flipped)

Liveness ==
    <>(declared /\ freed)

==========================================================================