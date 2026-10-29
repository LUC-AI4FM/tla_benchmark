---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,              \* number of nodes in the ring
    MaxPending      \* bound on pending messages per node (for model checking)

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxPendingAssumption == MaxPending \in Nat

Nodes == 0 .. (N - 1)

\* Successor of a node in the ring
Succ(i) == (i + 1) % N

VARIABLES
    active,               \* active[i] : TRUE iff node i is active
    pending,              \* pending[i] : number of messages pending at node i
    terminationDetected   \* TRUE iff global termination has been detected

vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------
\* Type correctness

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ terminationDetected \in BOOLEAN

\* Actual (global) termination: all nodes inactive and no messages in transit
Terminated ==
    \A i \in Nodes : ~active[i] /\ pending[i] = 0

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> 0 .. MaxPending]
    /\ terminationDetected \in {FALSE, Terminated}

-----------------------------------------------------------------------------
\* Actions

\* An active node becomes inactive
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, terminationDetected >>

\* An active node sends a message to its successor in the ring
SendMsg(i) ==
    /\ active[i]
    /\ LET j == Succ(i) IN
         pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

\* A node receives a pending message and becomes active
RcvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED terminationDetected

\* Termination is detected once all nodes are inactive with no pending messages
DetectTermination ==
    /\ ~terminationDetected
    /\ Terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

Next ==
    \/ \E i \in Nodes : Terminate(i) \/ SendMsg(i) \/ RcvMsg(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------
\* Safety properties

\* Detection implies actual termination
TDCorrect == terminationDetected => Terminated

\* Termination is stable once reached
Stable == [](Terminated => []Terminated)

\* Detection is stable once reached
DetectionStable == [](terminationDetected => []terminationDetected)

-----------------------------------------------------------------------------
\* Liveness property

\* Actual termination eventually leads to detection
Live == Terminated ~> terminationDetected

-----------------------------------------------------------------------------
\* Auxiliary invariants

\* If detected, no node is active
DetectedNoActive == terminationDetected => \A i \in Nodes : ~active[i]

\* If detected, no messages are pending
DetectedNoPending == terminationDetected => \A i \in Nodes : pending[i] = 0

\* Pending counts are non-negative
PendingNonNeg == \A i \in Nodes : pending[i] >= 0

Inv ==
    /\ TypeOK
    /\ TDCorrect
    /\ DetectedNoActive
    /\ DetectedNoPending
    /\ PendingNonNeg

-----------------------------------------------------------------------------
\* State constraint for bounded model checking

StateConstraint == \A i \in Nodes : pending[i] <= MaxPending

=============================================================================