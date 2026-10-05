--------------------------- MODULE TerminationDetection ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Node == 0..(N-1)

VARIABLES
    active,
    terminationDetected

vars == <<active, terminationDetected>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected = FALSE

Terminate(n) ==
    /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ terminationDetected' = terminationDetected

Wakeup(n, m) ==
    /\ active[n] = TRUE
    /\ n # m
    /\ active' = [active EXCEPT ![m] = TRUE]
    /\ terminationDetected' = terminationDetected

AllInactive ==
    \A n \in Node : active[n] = FALSE

DetectTermination ==
    /\ AllInactive
    /\ terminationDetected = FALSE
    /\ terminationDetected' = TRUE
    /\ active' = active

Next ==
    \/ \E n \in Node : Terminate(n)
    \/ \E n, m \in Node : Wakeup(n, m)
    \/ DetectTermination

Fairness == WF_vars(DetectTermination)

Spec == Init /\ [][Next]_vars /\ Fairness

Safety ==
    terminationDetected => AllInactive

Quiescence ==
    AllInactive /\ terminationDetected => [][AllInactive /\ terminationDetected]_vars

Liveness ==
    AllInactive ~> terminationDetected

Correctness ==
    /\ []Safety
    /\ Liveness

===================================================================================