---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Node

VARIABLE active
VARIABLE detected

vars == <<active, detected>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ detected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ detected = FALSE

Terminate(n) ==
    /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED detected

Wakeup(n, m) ==
    /\ active[n] = TRUE
    /\ n # m
    /\ active' = [active EXCEPT ![m] = TRUE]
    /\ UNCHANGED detected

AllInactive ==
    \A n \in Node : active[n] = FALSE

Detect ==
    /\ AllInactive
    /\ detected = FALSE
    /\ detected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E n \in Node : Terminate(n)
    \/ \E n, m \in Node : Wakeup(n, m)
    \/ Detect

Fairness == WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

Quiescence == AllInactive

Correctness == detected => Quiescence

Liveness == Quiescence ~> detected

=============================================================================