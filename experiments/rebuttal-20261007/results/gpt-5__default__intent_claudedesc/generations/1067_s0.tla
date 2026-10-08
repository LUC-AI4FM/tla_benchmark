--------------------------- MODULE TerminationRing ---------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES Active, detected

Nodes == 0..(N - 1)
AllInactive == Active = {}

TypeOK ==
  /\ Active \subseteq Nodes
  /\ detected \in BOOLEAN

Init ==
  /\ TypeOK
  /\ detected => AllInactive

Deactivate(i) ==
  /\ i \in Active
  /\ Active' = Active \ {i}
  /\ UNCHANGED detected

WakeUp(j, k) ==
  /\ j \in Active
  /\ k \in Nodes
  /\ k \notin Active
  /\ Active' = Active \cup {k}
  /\ UNCHANGED detected

Detect ==
  /\ AllInactive
  /\ detected' = TRUE
  /\ UNCHANGED Active

Next ==
  \/ \E i \in Active: Deactivate(i)
  \/ \E j \in Active: \E k \in Nodes \ Active: WakeUp(j, k)
  \/ Detect

vars == << Active, detected >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Detect)

(*
 Safety properties:
  1) No false detection: detection implies genuine termination.
  2) Stability of termination: once all inactive, they remain so forever.
  3) Type correctness is maintained forever.
*)
NoFalseReport ==
  [] (detected => AllInactive)

Stability ==
  [] (AllInactive => [] AllInactive)

TypeInvariant ==
  [] TypeOK

(*
 Liveness property:
  Whenever all nodes are inactive, termination is eventually detected.
*)
TerminationEventuallyReported ==
  [] (AllInactive => <> detected)

=============================================================================