----------------------------- MODULE TerminationDetectionRing -----------------------------

EXTENDS Naturals

CONSTANTS
    N,            \* Number of nodes in the ring
    MaxPending    \* Per-node upper bound on pending messages (for bounded model checking)

ASSUME N \in Nat /\ N >= 1
ASSUME MaxPending \in Nat

\* Node identifiers
Node == 0 .. (N - 1)

\* Ring successor
Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1

\* State variables
VARIABLES
    active,    \* [Node -> BOOLEAN], whether node i is active
    pending,   \* [Node -> Nat],     number of pending (undelivered) messages destined to node i
    detected   \* BOOLEAN,           whether global termination has been detected

vars == << active, pending, detected >>

\* Derived predicates
AllTerminated ==
    /\ \A i \in Node: ~active[i]
    /\ \A i \in Node: pending[i] = 0

\* State constraint for bounded model checking (per-node bound)
StateConstraint == \A i \in Node: pending[i] <= MaxPending

\* Typing invariant
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ detected \in BOOLEAN

\* Initial states
Init ==
    /\ TypeOK
    /\ detected = FALSE
    /\ StateConstraint

\* Actions
Send(i) ==
    /\ i \in Node
    /\ active[i] = TRUE
    /\ pending[Succ(i)] < MaxPending
    /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
    /\ UNCHANGED << active, detected >>

Receive(i) ==
    /\ i \in Node
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active'  = [active  EXCEPT ![i] = TRUE]
    /\ UNCHANGED detected

Terminate(i) ==
    /\ i \in Node
    /\ active[i] = TRUE
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, detected >>

DetectTermination ==
    /\ AllTerminated
    /\ ~detected
    /\ detected' = TRUE
    /\ UNCHANGED << active, pending >>

Next ==
    /\ \/ \E i \in Node: Send(i)
       \/ \E i \in Node: Receive(i)
       \/ \E i \in Node: Terminate(i)
       \/ DetectTermination
    /\ StateConstraint'

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(DetectTermination)

\* Safety invariants
DetectionSound == [](detected => AllTerminated)

\* Stability properties (safety-style temporal properties)
TerminationStable == [](AllTerminated => []AllTerminated)
DetectionStable   == [](detected => []detected)

\* Liveness: actual termination leads to eventual detection under WF on DetectTermination
TerminationLeadsToDetection == AllTerminated ~> detected

=============================================================================