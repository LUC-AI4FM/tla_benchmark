------------------------------ MODULE TerminationDetectionRing ------------------------------

EXTENDS Naturals, TLC

CONSTANTS
  N,          \* number of nodes in the ring
  MaxPending  \* bound for state constraint (e.g., 3)

ASSUME
  /\ N \in Nat \ {0}
  /\ MaxPending \in Nat

VARIABLES
  active,               \* [1..N -> BOOLEAN]
  pending,              \* [1..N -> Nat]
  terminationDetected   \* BOOLEAN

Nodes == 1..N

vars == << active, pending, terminationDetected >>

(*
  Basic typing and termination predicates
*)
TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ pending \in [Nodes -> Nat]
  /\ terminationDetected \in BOOLEAN

NoPending == \A i \in Nodes: pending[i] = 0
AllInactive == \A i \in Nodes: ~active[i]
Terminated == AllInactive /\ NoPending

(*
  Initialization:
  - pending is zero everywhere
  - active is arbitrary per node
  - terminationDetected may be true only if the system is truly terminated
*)
Init ==
  /\ TypeOK
  /\ pending = [i \in Nodes |-> 0]
  /\ terminationDetected \in BOOLEAN
  /\ (terminationDetected => Terminated)

(*
  Actions
*)

\* An active node deactivates; it may set terminationDetected to TRUE iff the resulting state is truly terminated.
Terminate(n) ==
  /\ n \in Nodes
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ pending' = pending
  /\ \/ terminationDetected' = terminationDetected
     \/ /\ Terminated'
        /\ terminationDetected' = TRUE

\* An active node sends a message to any destination node, incrementing its pending count.
SendMsg(s, d) ==
  /\ s \in Nodes
  /\ d \in Nodes
  /\ active[s]
  /\ pending' = [pending EXCEPT ![d] = @ + 1]
  /\ UNCHANGED << active, terminationDetected >>

\* A node with pending messages consumes one and becomes active.
RcvMsg(n) ==
  /\ n \in Nodes
  /\ pending[n] > 0
  /\ pending' = [pending EXCEPT ![n] = @ - 1]
  /\ active'  = [active  EXCEPT ![n] = TRUE]
  /\ terminationDetected' = terminationDetected

\* Detects termination whenever it truly holds.
DetectTermination ==
  /\ Terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED << active, pending >>

Next ==
  \/ \E n \in Nodes: Terminate(n)
  \/ \E s \in Nodes: \E d \in Nodes: SendMsg(s, d)
  \/ \E n \in Nodes: RcvMsg(n)
  \/ DetectTermination

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DetectTermination)

(*
  Properties
*)

\* Safety: detection implies actual termination
Safe == terminationDetected => Terminated
Safety == []Safe

\* Inductive invariant for verification (e.g., Apalache)
IndInv == TypeOK /\ Safe

\* Liveness: once truly terminated, detection eventually occurs
Live == [](Terminated => <> terminationDetected)

\* Quiescence: once terminated, it remains terminated
Quiescence == [](Terminated => []Terminated)

\* Action-formula variant of quiescence (useful as a step property)
QuiescenceAct == Terminated => Terminated'

\* State constraint (for bounded model checking, e.g., MaxPending = 3)
StateConstraint == \A i \in Nodes: pending[i] <= MaxPending

CONSTRAINT StateConstraint

===========================================================================================