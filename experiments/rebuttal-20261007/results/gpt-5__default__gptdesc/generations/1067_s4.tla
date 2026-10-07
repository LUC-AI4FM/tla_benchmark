---- MODULE TerminationDetectionRing ----
EXTENDS Naturals

CONSTANTS Node, Succ

(*
  Assumptions:
  - Node is a nonempty set of node identifiers.
  - Succ is a bijection Node -> Node (each node has a unique successor and
    each node is the successor of exactly one node).
*)
RingAssumptions ==
  /\ Node /= {}
  /\ Succ \in [Node -> Node]
  /\ \A m, n \in Node: Succ[m] = Succ[n] => m = n
  /\ \A y \in Node: \E x \in Node: Succ[x] = y

ASSUME RingAssumptions

VARIABLES active, detected

Vars == << active, detected >>

TypeOK ==
  /\ active \subseteq Node
  /\ detected \in BOOLEAN

Init ==
  /\ TypeOK
  /\ detected = FALSE
  /\ active \subseteq Node

Quiescent ==
  active = {}

(*
  Actions:
  - Terminate(n): an active node n becomes inactive.
  - Wake(n): an active node n wakes up its successor m = Succ[n] if m is inactive.
  - Detect: if all nodes are inactive and detection not yet set, set detected = TRUE.
*)
Terminate(n) ==
  /\ ~detected
  /\ n \in active
  /\ active' = active \ {n}
  /\ UNCHANGED detected

Wake(n) ==
  /\ ~detected
  /\ n \in active
  /\ LET m == Succ[n] IN
     /\ m \in Node
     /\ m \notin active
     /\ active' = active \cup {m}
  /\ UNCHANGED detected

Detect ==
  /\ ~detected
  /\ Quiescent
  /\ UNCHANGED active
  /\ detected' = TRUE

Next ==
  \/ \E n \in Node: Terminate(n)
  \/ \E n \in Node: Wake(n)
  \/ Detect

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Detect)

(*
  Safety invariants:
  - TypeOK always holds.
  - No false detection: if detected then all nodes are inactive.
  - Detection is sticky: once detected, it remains detected.
*)
InvTypeOK ==
  []TypeOK

InvNoFalseDetection ==
  [](detected => Quiescent)

InvDetectionSticky ==
  [](detected => []detected)

(*
  Enabledness (safety-style) property for detection:
  - Whenever the system is quiescent and not yet detected, the Detect action is enabled.
*)
DetectEnabledWhenQuiescent ==
  []((Quiescent /\ ~detected) => ENABLED Detect)

(*
  Liveness-style property (completeness of detection):
  - If from some point onward the system remains quiescent, then detection eventually occurs.
*)
DetectionCompleteness ==
  (<>[]Quiescent) => <>detected

====