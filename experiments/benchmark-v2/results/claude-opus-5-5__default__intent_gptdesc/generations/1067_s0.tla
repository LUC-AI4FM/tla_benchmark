------------------------------ MODULE RingTerminationDetection ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NPositive == N \in Nat /\ N > 0

Node == 0 .. N-1

\* Logical ring structure. The abstract model does not prescribe a detection
\* algorithm, so the ring is described but not used to constrain transitions.
Succ(i) == (i + 1) % N

VARIABLES active, terminationDetected

vars == << active, terminationDetected >>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

AllInactive == \A i \in Node : ~active[i]

---------------------------------------------------------------------------------------------

\* Any initial active/inactive assignment is allowed.
Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected = FALSE

\* An active process locally decides to become inactive.
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED terminationDetected

\* An active process sends an activation to another process.
\* With synchronous delivery, the receiver becomes active immediately.
\* This may reawaken an inactive process.
SendMsg(i, j) ==
    /\ i # j
    /\ active[i]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminationDetected

\* The global detection event. It may be raised only when the system is quiescent.
DetectTermination ==
    /\ AllInactive
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : SendMsg(i, j)
    \/ DetectTermination

\* Weak fairness on detection ensures it cannot be perpetually deferred.
Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

---------------------------------------------------------------------------------------------

\* Safety: once termination is declared, the system is quiescent.
TerminationDetectedSafe == terminationDetected => AllInactive

Safety == [](terminationDetected => AllInactive)

\* Quiescence persistence: once all processes are inactive, they stay inactive.
Quiescence == [](AllInactive => []AllInactive)

\* Liveness: whenever the system is quiescent, detection eventually happens.
Liveness == AllInactive ~> terminationDetected

THEOREM Spec => []TypeOK
THEOREM Spec => Safety
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
=============================================================================================