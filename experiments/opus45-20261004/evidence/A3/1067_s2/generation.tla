---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node

VARIABLES active, terminationDetected

vars == <<active, terminationDetected>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected = FALSE

\* An active node terminates (becomes inactive)
Terminate(n) ==
    /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ terminationDetected' = terminationDetected

\* An active node wakes up another node (makes it active)
Wakeup(n, m) ==
    /\ active[n] = TRUE
    /\ n # m
    /\ active' = [active EXCEPT ![m] = TRUE]
    /\ terminationDetected' = FALSE

\* Detection step: set terminationDetected when all nodes are inactive
Detect ==
    /\ \A n \in Node : active[n] = FALSE
    /\ terminationDetected = FALSE
    /\ terminationDetected' = TRUE
    /\ active' = active

\* Stuttering step
Stutter ==
    UNCHANGED vars

Next ==
    \/ \E n \in Node : Terminate(n)
    \/ \E n, m \in Node : Wakeup(n, m)
    \/ Detect
    \/ Stutter

\* Fairness condition on the detection action
Fairness == WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

\* All nodes are inactive (quiescence)
Quiescent == \A n \in Node : active[n] = FALSE

\* Safety: If termination is detected, then all nodes must be inactive
Safety == terminationDetected => Quiescent

\* Correctness: terminationDetected is only true when system is quiescent
Correctness == [](terminationDetected => Quiescent)

\* Liveness: If all nodes become and stay inactive, termination will eventually be detected
Liveness == [](Quiescent => <>terminationDetected)

\* Stable detection: Once detected while quiescent, stays detected until activity resumes
StableDetection == []((terminationDetected /\ Quiescent) => 
                      (terminationDetected \/ ~Quiescent))

===================================================================================