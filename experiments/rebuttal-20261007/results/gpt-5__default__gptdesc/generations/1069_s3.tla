----------------------------- MODULE TerminationDetectionRing -----------------------------

EXTENDS Naturals

CONSTANTS
  N,           \* number of nodes in the ring (N >= 1)
  MaxPending   \* per-node bound on pending messages (for bounded model checking)

ASSUME N \in Nat /\ N >= 1 /\ MaxPending \in Nat

(*
  Indexing and basic definitions
*)
Nodes == 0..(N - 1)

NextOf(i) == IF i = N - 1 THEN 0 ELSE i + 1

VARIABLES
  Active,    \* function Nodes -> BOOLEAN: whether node i is active
  Pending,   \* function Nodes -> Nat: number of pending messages for node i
  Detected   \* BOOLEAN: whether global termination has been detected

vars == << Active, Pending, Detected >>

(*
  State predicates
*)
AllInactive == \A i \in Nodes: ~Active[i]
AllZeroPending == \A i \in Nodes: Pending[i] = 0
AllTerminated == AllInactive /\ AllZeroPending

TypeInv ==
  /\ Active \in [Nodes -> BOOLEAN]
  /\ Pending \in [Nodes -> Nat]
  /\ Detected \in BOOLEAN

BoundInv ==
  \A i \in Nodes: Pending[i] <= MaxPending

(*
  A state-constraint predicate suitable for TLC's STATE CONSTRAINT
*)
StateCons == BoundInv

(*
  Initial states
*)
Init ==
  /\ TypeInv
  /\ Detected = FALSE
  /\ BoundInv

(*
  System actions
*)
Send(i) ==
  /\ i \in Nodes
  /\ Active[i]
  /\ Active' = Active
  /\ Pending' = [Pending EXCEPT ![NextOf(i)] = @ + 1]
  /\ UNCHANGED Detected

Receive(i) ==
  /\ i \in Nodes
  /\ Pending[i] > 0
  /\ Pending' = [Pending EXCEPT ![i] = @ - 1]
  /\ Active' = [Active EXCEPT ![i] = TRUE]
  /\ UNCHANGED Detected

Terminate(i) ==
  /\ i \in Nodes
  /\ Active[i]
  /\ Pending[i] = 0
  /\ Active' = [Active EXCEPT ![i] = FALSE]
  /\ UNCHANGED << Pending, Detected >>

DetectTermination ==
  /\ ~Detected
  /\ AllTerminated
  /\ Detected' = TRUE
  /\ UNCHANGED << Active, Pending >>

Next ==
  \/ (\E i \in Nodes: Send(i))
  \/ (\E i \in Nodes: Receive(i))
  \/ (\E i \in Nodes: Terminate(i))
  \/ DetectTermination

(*
  Full behavior spec with weak fairness for DetectTermination
*)
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DetectTermination)

(*
  Safety properties (invariants/always properties)
*)
DetectionSoundness ==
  [](Detected => AllTerminated)

TerminationStable ==
  [](AllTerminated => []AllTerminated)

DetectionStable ==
  [](Detected => []Detected)

DetectionEnabledWhenTerminated ==
  []((~Detected /\ AllTerminated) => Enabled DetectTermination)

(*
  Liveness: actual termination leads to eventual detection
*)
TerminationLeadsToDetection ==
  AllTerminated ~> Detected

==========================================================================================