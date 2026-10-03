---- MODULE TerminationRing ----
EXTENDS TLA

CONSTANT Node

(*
  Abstract termination detection over a set of nodes Node.
  Each node n ∈ Node has a boolean activity flag active[n].
  The boolean detected indicates whether global termination has been detected.
*)

ASSUME Node # {}

VARIABLES active, detected

vars == << active, detected >>

AllInactive(a) == ∀ n ∈ Node: ~a[n]
SomeActive(a) == ∃ n ∈ Node: a[n]

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ detected \in BOOLEAN

Init ==
  /\ TypeOK
  /\ detected = FALSE

DoTerminate(n) ==
  /\ ~detected
  /\ n \in Node
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED detected

Terminate ==
  ∃ n \in Node: DoTerminate(n)

DoWakeUp(j) ==
  /\ ~detected
  /\ j \in Node
  /\ ∃ i \in Node: active[i]
  /\ ~active[j]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED detected

WakeUp ==
  ∃ j \in Node: DoWakeUp(j)

Detect ==
  /\ ~detected
  /\ AllInactive(active)
  /\ detected' = TRUE
  /\ UNCHANGED active

Next ==
  Terminate \/ WakeUp \/ Detect

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Detect)

(*
  Temporal properties for model checking.
  - Correctness: detection implies global inactivity.
  - Quiescence: eventually the system is permanently inactive and detection holds.
  - Liveness: if the system eventually becomes permanently inactive, detection eventually occurs.
*)
Correctness ==
  [] (detected => AllInactive(active))

Quiescence ==
  <>[] (AllInactive(active) /\ detected)

Liveness ==
  (<>[] AllInactive(active)) => (<> detected)
=============================