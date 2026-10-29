---------------------------- MODULE AsyncTerminationDetection ----------------------------
(***************************************************************************)
(* Abstract asynchronous termination detection for a ring of N nodes.      *)
(* Each node is active or inactive and has a count of pending (in-transit) *)
(* messages addressed to it.  Active nodes may send messages to their ring *)
(* successor or become inactive.  A node with pending messages may receive *)
(* one, which activates it.  Termination may be detected once all nodes    *)
(* are inactive and no messages are pending.                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N,            \* number of nodes in the ring
          MaxPending    \* bound on pending messages per node (for model checking)

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxPendingAssumption == MaxPending \in Nat

Nodes == 0 .. N-1

Succ(i) == (i + 1) % N

VARIABLES
    active,               \* active[i] : is node i active?
    pending,              \* pending[i] : number of messages pending at node i
    terminationDetected   \* has global termination been detected?

vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ terminationDetected \in BOOLEAN

\* Actual global termination: all nodes inactive and no messages in transit
terminated == \A i \in Nodes : ~active[i] /\ pending[i] = 0

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> 0 .. MaxPending]
    /\ terminationDetected \in {FALSE, terminated}

\* An active node becomes inactive
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, terminationDetected >>

\* An active node sends a message to its successor in the ring
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
    \/ \E i \in Nodes : Terminate(i) \/ SendMsg(i) \/ RcvMsg(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------
(* Properties *)

\* Safety: detection implies actual termination
TerminationDetection == terminationDetected => terminated

\* Termination is stable once reached
StableTermination == [][terminated => terminated']_vars

\* Detection is stable once it has occurred
StableDetection == [][terminationDetected => terminationDetected']_vars

\* Liveness: actual termination eventually leads to detection
Liveness == terminated ~> terminationDetected

\* Auxiliary invariants
PendingNonNegative == \A i \in Nodes : pending[i] >= 0

DetectedImpliesQuiescent ==
    terminationDetected => \A i \in Nodes : ~active[i] /\ pending[i] = 0

\* State constraint for bounded model checking
StateConstraint == \A i \in Nodes : pending[i] <= MaxPending

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => StableTermination
THEOREM Spec => Liveness

=============================================================================