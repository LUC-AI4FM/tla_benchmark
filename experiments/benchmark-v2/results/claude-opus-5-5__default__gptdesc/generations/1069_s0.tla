---------------------------- MODULE AsyncTerminationDetection ----------------------------
(***************************************************************************)
(* Abstract specification of asynchronous termination detection for a     *)
(* ring of N nodes. Each node is active or inactive and has a count of     *)
(* pending (in-flight) messages addressed to it. Global termination holds  *)
(* when every node is inactive and no messages are pending. Detection may  *)
(* occur only once global termination holds.                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N,           \* number of nodes in the ring
          MaxPending   \* bound on pending messages per node (for model checking)

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxPendingAssumption == MaxPending \in Nat

Nodes == 0 .. N-1

Succ(i) == (i + 1) % N

VARIABLES active,               \* active[i] : is node i active?
          pending,              \* pending[i] : number of messages pending at node i
          terminationDetected   \* has global termination been detected?

vars == <<active, pending, terminationDetected>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ terminationDetected \in BOOLEAN

terminated ==
    \A i \in Nodes : ~active[i] /\ pending[i] = 0

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [i \in Nodes |-> 0]
    /\ terminationDetected \in {FALSE, terminated}

\* An active node becomes inactive.
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, terminationDetected>>

\* An active node sends a message to its successor on the ring.
SendMsg(i) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
    /\ UNCHANGED <<active, terminationDetected>>

\* A node receives a pending message and becomes active.
RcvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED terminationDetected

\* Termination is detected once all nodes are inactive with no pending messages.
DetectTermination ==
    /\ terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E i \in Nodes : Terminate(i) \/ SendMsg(i) \/ RcvMsg(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Detection implies actual termination.
Safe == terminationDetected => terminated

\* Once detected, detection is never revoked.
DetectionStable == [][terminationDetected => terminationDetected']_vars

\* Termination is stable once reached.
Quiescence == [](terminated => []terminated)

(* Liveness property *)

\* Actual termination eventually leads to detection.
Live == terminated ~> terminationDetected

-----------------------------------------------------------------------------
(* Auxiliary invariants *)

PendingNonNeg == \A i \in Nodes : pending[i] >= 0

DetectedImpliesNoActive ==
    terminationDetected => \A i \in Nodes : ~active[i]

DetectedImpliesNoPending ==
    terminationDetected => \A i \in Nodes : pending[i] = 0

Inv == TypeOK /\ Safe /\ PendingNonNeg
       /\ DetectedImpliesNoActive /\ DetectedImpliesNoPending

-----------------------------------------------------------------------------
(* State constraint for bounded model checking *)

StateConstraint == \A i \in Nodes : pending[i] <= MaxPending

THEOREM Spec => []Inv
THEOREM Spec => Quiescence
THEOREM Spec => Live
=============================================================================