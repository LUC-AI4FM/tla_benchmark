---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxPending

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxPendingAssumption == MaxPending \in Nat

Node == 0 .. N-1

VARIABLES
    active,               \* active[i] : is node i currently active?
    pending,              \* pending[i] : number of messages pending at node i
    terminationDetected   \* has global termination been detected?

vars == <<active, pending, terminationDetected>>

------------------------------------------------------------------------------------------
\* Ring successor of node i
Succ(i) == (i + 1) % N

\* Actual global termination: all nodes inactive and no pending messages
Terminated == \A i \in Node : ~active[i] /\ pending[i] = 0

------------------------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> {0}]
    /\ terminationDetected = FALSE

\* An active node becomes inactive
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, terminationDetected>>

\* An active node sends a message to its successor on the ring
SendMsg(i) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
    /\ UNCHANGED <<active, terminationDetected>>

\* A node receives a pending message and becomes active
RcvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED terminationDetected

\* Detection may occur once all nodes are inactive with no pending messages
DetectTermination ==
    /\ ~terminationDetected
    /\ \A i \in Node : ~active[i] /\ pending[i] = 0
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E i \in Node : Terminate(i) \/ SendMsg(i) \/ RcvMsg(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

------------------------------------------------------------------------------------------
\* Safety: detection implies actual termination
TDCorrect == terminationDetected => Terminated

\* Auxiliary invariants
PendingNonNegative == \A i \in Node : pending[i] >= 0

DetectedStable == terminationDetected => \A i \in Node : ~active[i]

Inv == TypeOK /\ TDCorrect /\ PendingNonNegative /\ DetectedStable

\* Termination is stable once reached
TerminationStable == [][Terminated => Terminated']_vars

\* Detection, once made, is never revoked
DetectionStable == [][terminationDetected => terminationDetected']_vars

\* Liveness: actual termination leads to eventual detection
Liveness == Terminated ~> terminationDetected

\* State constraint for bounded model checking
StateConstraint == \A i \in Node : pending[i] <= MaxPending

THEOREM Spec => []Inv
THEOREM Spec => TerminationStable
THEOREM Spec => Liveness
==========================================================================================