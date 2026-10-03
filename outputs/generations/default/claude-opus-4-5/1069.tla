---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES
    active,         \* active[i] = TRUE iff node i is active
    pending,        \* pending[i] = count of pending messages for node i
    terminationDetected  \* TRUE iff termination has been detected

vars == <<active, pending, terminationDetected>>

Nodes == 0..(N-1)

\* All nodes are inactive and no messages are pending
Terminated ==
    /\ \A i \in Nodes : active[i] = FALSE
    /\ \A i \in Nodes : pending[i] = 0

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [i \in Nodes |-> 0]
    /\ terminationDetected = FALSE

\* A node becomes inactive (terminates locally)
Terminate(i) ==
    /\ active[i] = TRUE
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, terminationDetected>>

\* An active node sends a message to another node
SendMsg(i, j) ==
    /\ active[i] = TRUE
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED <<active, terminationDetected>>

\* A node receives a pending message and becomes active
ReceiveMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED terminationDetected

\* Termination is detected when all nodes are inactive and no messages pending
DetectTermination ==
    /\ Terminated
    /\ terminationDetected = FALSE
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E i \in Nodes : Terminate(i)
    \/ \E i, j \in Nodes : SendMsg(i, j)
    \/ \E i \in Nodes : ReceiveMsg(i)
    \/ DetectTermination

\* Fairness: weak fairness on DetectTermination for liveness
Fairness == WF_vars(DetectTermination)

Spec == Init /\ [][Next]_vars /\ Fairness

\* ----- Safety Invariants -----

\* If termination is detected, then actual termination holds
DetectionSafety == terminationDetected => Terminated

\* ----- Stability Property -----

\* Once terminated (all inactive and no pending), it stays terminated
\* This is expressed as: if Terminated and no enabled actions that change it
\* We express stability as an invariant on the transition relation
StableTermination ==
    (Terminated /\ terminationDetected) => [][Terminated /\ terminationDetected]_vars

\* ----- Auxiliary Invariants -----

\* Pending counts are non-negative (follows from TypeOK but explicit)
PendingNonNegative == \A i \in Nodes : pending[i] >= 0

\* If detection happened, it stays (detection is monotonic)
DetectionMonotonic == [][terminationDetected => terminationDetected']_vars

\* ----- Liveness Properties -----

\* If actual termination holds, eventually detection will occur
TerminationLeadsToDetection == Terminated ~> terminationDetected

\* ----- State Constraint for Bounded Model Checking -----

StateConstraint ==
    /\ \A i \in Nodes : pending[i] <= 3

\* ----- Theorems / Properties to Check -----

THEOREM SafetyTheorem == Spec => []DetectionSafety

THEOREM TypeCorrectness == Spec => []TypeOK

THEOREM LivenessTheorem == Spec => TerminationLeadsToDetection

=============================================================================