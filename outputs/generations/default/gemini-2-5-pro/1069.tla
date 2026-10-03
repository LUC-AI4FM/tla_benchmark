---- MODULE RingTermination ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxPending

ASSUME N \in Nat \land N > 0
ASSUME MaxPending \in Nat \land MaxPending > 0

VARIABLES
    \* active[i] is TRUE iff node i is active.
    active,
    \* pending[i] is the number of messages sent by node i that are in transit.
    pending,
    \* detected is TRUE iff global termination has been detected.
    detected

Node == 0..N-1
vars == <<active, pending, detected>>

-----------------------------------------------------------------------------
(*-- Definitions --*)

\* The predecessor of node i in the ring.
Pred(i) == (i - 1 + N) % N

\* The condition for actual global termination: all nodes are inactive and
\* no messages are in transit.
ActualTermination ==
    /\ \A i \in Node : ~active[i]
    /\ \A i \in Node : pending[i] = 0

-----------------------------------------------------------------------------
(*-- Initial State --*)

Init ==
    /\ active = [i \in Node |-> TRUE]
    /\ pending = [i \in Node |-> 0]
    /\ detected = FALSE

-----------------------------------------------------------------------------
(*-- State Transitions (Actions) --*)

\* An active node i spontaneously becomes inactive.
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, detected>>

\* An active node i sends a message to its successor. This increases the
\* count of messages sent by i that are pending receipt.
Send(i) ==
    /\ active[i]
    /\ pending[i] < MaxPending
    /\ pending' = [pending EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, detected>>

\* A node i receives a message from its predecessor. Upon receiving a
\* message, a node becomes active.
Receive(i) ==
    /\ pending[Pred(i)] > 0
    /\ pending' = [pending EXCEPT ![Pred(i)] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<detected>>

\* The system detects global termination. This can only happen when the
\* ActualTermination condition is met.
DetectTermination ==
    /\ ~detected
    /\ ActualTermination
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i \in Node : Send(i)
    \/ \E i \in Node : Receive(i)
    \/ DetectTermination

-----------------------------------------------------------------------------
(*-- Specification --*)

Spec == Init /\ [][Next]_vars

\* Weak fairness on the DetectTermination action is required for liveness.
\* It states that if detection is continuously possible, it must eventually occur.
Fairness == WF_vars(DetectTermination)

-----------------------------------------------------------------------------
(*-- Properties and Invariants --*)

\* Auxiliary Invariant: The state variables have the correct types.
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> 0..MaxPending]
    /\ detected \in BOOLEAN

\* Safety: If termination is detected, then the system must actually be
\* in a terminated state.
DetectionImpliesTermination == detected => ActualTermination

\* Safety: Once the system reaches a globally terminated state, it remains
\* in a terminated state forever. (The `detected` flag may still change).
TerminationIsStable == ActualTermination => []ActualTermination

\* Liveness: If the system reaches a globally terminated state, termination
\* will eventually be detected. This property relies on the Fairness assumption.
TerminationLeadsToDetection == ActualTermination ~> detected

=============================================================================