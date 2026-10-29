---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Naturals

CONSTANTS N, MaxPending

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxPendingAssumption == MaxPending \in Nat

Node == 1 .. N

\* Successor of node i on the ring
Succ(i) == IF i = N THEN 1 ELSE i + 1

VARIABLES
    active,               \* active[i] : activation status of node i
    pending,              \* pending[i] : number of messages pending at node i
    terminationDetected   \* whether global termination has been detected

vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected \in BOOLEAN

terminated ==
    \A i \in Node : ~active[i] /\ pending[i] = 0

-----------------------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [i \in Node |-> 0]
    /\ terminationDetected = FALSE

\* An active node becomes inactive
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, terminationDetected >>

\* An active node sends a message to its successor on the ring
SendMsg(i) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

\* A node receives a pending message and becomes active
RcvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED terminationDetected

\* Termination is detected once all nodes are inactive with no pending messages
DetectTermination ==
    /\ terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

Next ==
    \/ \E i \in Node : Terminate(i) \/ SendMsg(i) \/ RcvMsg(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------------------
\* Safety properties

\* Detection implies actual termination
TerminationDetectedSafe == terminationDetected => terminated

\* Termination is stable once reached
Stable == [](terminated => []terminated)

\* Once detected, detection remains
DetectionStable == [](terminationDetected => []terminationDetected)

\* Auxiliary invariants
PendingNonNegative == \A i \in Node : pending[i] >= 0

DetectedNoActivity ==
    terminationDetected => \A i \in Node : ~active[i]

DetectedNoPending ==
    terminationDetected => \A i \in Node : pending[i] = 0

Inv ==
    /\ TypeOK
    /\ TerminationDetectedSafe
    /\ PendingNonNegative
    /\ DetectedNoActivity
    /\ DetectedNoPending

-----------------------------------------------------------------------------------------
\* Liveness property

\* Actual termination eventually leads to detection
Live == terminated ~> terminationDetected

-----------------------------------------------------------------------------------------
\* State constraint for bounded model checking

StateConstraint == \A i \in Node : pending[i] <= MaxPending

THEOREM Spec => []Inv
THEOREM Spec => Stable
THEOREM Spec => Live

=========================================================================================