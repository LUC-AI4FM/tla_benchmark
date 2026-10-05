---------------------------- MODULE prisoners_switches ----------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS Prisoner, p2, p3

ASSUME Prisoner = {p2, p3}
ASSUME p2 \in Prisoner /\ p3 \in Prisoner
ASSUME p2 /= p3

VARIABLES
    switchA,
    switchB,
    counter,
    counterTally,
    hasVisited,
    hasContributed,
    done

vars == <<switchA, switchB, counter, counterTally, hasVisited, hasContributed, done>>

N == Cardinality(Prisoner)

TypeOK ==
    /\ switchA \in {0, 1}
    /\ switchB \in {0, 1}
    /\ counter \in Prisoner
    /\ counterTally \in 0..N
    /\ hasVisited \subseteq Prisoner
    /\ hasContributed \subseteq (Prisoner \ {counter})
    /\ done \in BOOLEAN

Init ==
    /\ switchA = 0
    /\ switchB = 0
    /\ counter = p2
    /\ counterTally = 1
    /\ hasVisited = {}
    /\ hasContributed = {}
    /\ done = FALSE

CounterStep(p) ==
    /\ p = counter
    /\ ~done
    /\ hasVisited' = hasVisited \cup {p}
    /\ IF switchA = 1
       THEN /\ switchA' = 0
            /\ counterTally' = counterTally + 1
            /\ IF counterTally + 1 = N
               THEN done' = TRUE
               ELSE done' = FALSE
            /\ UNCHANGED <<switchB, hasContributed>>
       ELSE /\ switchB' = 1 - switchB
            /\ UNCHANGED <<switchA, counterTally, done, hasContributed>>
    /\ UNCHANGED counter

NonCounterStep(p) ==
    /\ p /= counter
    /\ ~done
    /\ hasVisited' = hasVisited \cup {p}
    /\ IF p \notin hasContributed /\ switchA = 0
       THEN /\ switchA' = 1
            /\ hasContributed' = hasContributed \cup {p}
            /\ UNCHANGED switchB
       ELSE /\ switchB' = 1 - switchB
            /\ UNCHANGED <<switchA, hasContributed>>
    /\ UNCHANGED <<counter, counterTally, done>>

PrisonerStep(p) ==
    \/ CounterStep(p)
    \/ NonCounterStep(p)

Next ==
    \E p \in Prisoner : PrisonerStep(p)

Fairness ==
    \A p \in Prisoner : WF_vars(PrisonerStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

CountInvariant ==
    /\ counterTally = 1 + Cardinality(hasContributed)
    /\ hasContributed \subseteq (Prisoner \ {counter})
    /\ (switchA = 1) => (\E p \in Prisoner \ {counter} : 
                          p \in hasContributed /\ 
                          counterTally = Cardinality(hasContributed))

Safety ==
    done => (hasVisited = Prisoner)

AllVisited == hasVisited = Prisoner

Liveness == <>done

=============================================================================