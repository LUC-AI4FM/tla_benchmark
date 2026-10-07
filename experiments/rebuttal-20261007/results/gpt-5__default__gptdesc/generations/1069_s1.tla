------------------------------ MODULE TerminationDetectionRing ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  N,          \* number of nodes in the ring (N >= 1)
  MaxMsgs,    \* per-node bound on pending messages (for bounded model checking)
  MaxTotal    \* global bound on total pending messages (for bounded model checking)

ASSUME N \in Nat \ {0}
ASSUME MaxMsgs \in Nat
ASSUME MaxTotal \in Nat

\* Nodes are arranged in a ring
Nodes == 1..N
Succ(i) == IF i < N THEN i + 1 ELSE 1

VARIABLES
  active,     \* [Nodes -> BOOLEAN], whether node i is currently active
  pending,    \* [Nodes -> 0..MaxMsgs], number of pending (not yet received) messages for node i
  detected    \* BOOLEAN, whether global termination has been detected

vars == << active, pending, detected >>

\* System is terminated iff all nodes are inactive and no pending messages remain
Terminated ==
  /\ \A i \in Nodes: ~active[i]
  /\ \A i \in Nodes: pending[i] = 0

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ pending \in [Nodes -> 0..MaxMsgs]
  /\ detected = FALSE

Send(i) ==
  /\ i \in Nodes
  /\ active[i]
  /\ pending[Succ(i)] < MaxMsgs
  /\ active' = active
  /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
  /\ detected' = detected

Receive(i) ==
  /\ i \in Nodes
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ LET a == [active EXCEPT ![i] = TRUE]
     IN active' \in { active, a }
  /\ detected' = detected

Terminate(i) ==
  /\ i \in Nodes
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED << pending, detected >>

DetectTermination ==
  /\ ~detected
  /\ Terminated
  /\ detected' = TRUE
  /\ UNCHANGED << active, pending >>

Skip == UNCHANGED vars

Next ==
  \/ \E i \in Nodes: Send(i)
  \/ \E i \in Nodes: Receive(i)
  \/ \E i \in Nodes: Terminate(i)
  \/ DetectTermination
  \/ Skip

Spec == Init /\ [] [Next]_vars /\ WF_vars(DetectTermination)

\* Auxiliary definitions and state constraint for bounded model checking
RECURSIVE Sum(_,_)
Sum(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE e \in S: TRUE IN f[x] + Sum(S \ {x}, f)

TotalPending == Sum(Nodes, pending)
NodeBound == \A i \in Nodes: pending[i] <= MaxMsgs
TotalBound == TotalPending <= MaxTotal
StateConstraint == NodeBound /\ TotalBound

\* Safety invariants
TypeInv ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ pending \in [Nodes -> 0..MaxMsgs]
  /\ detected \in BOOLEAN

NoNegativePending == \A i \in Nodes: pending[i] >= 0

\* Detection implies actual termination (safety)
DetectedImpliesActual == [](detected => Terminated)

\* Stability properties
\* Once detected, it remains detected
DetectionStable == [](detected => [] detected)
\* Once actual termination is reached, it remains so
TerminationStable == [](Terminated => [] Terminated)

\* Liveness: actual termination leads to eventual detection
TerminationLeadsToDetection == Terminated ~> detected

=============================================================================