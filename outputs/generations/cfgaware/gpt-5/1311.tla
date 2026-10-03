------------------------------ MODULE GCDLoop ------------------------------

EXTENDS Naturals

VARIABLES u, v, pc

vars == << u, v, pc >>

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "Loop"

Swap ==
  /\ pc = "Loop"
  /\ u > 0
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ pc' = "Loop"

Sub ==
  /\ pc = "Loop"
  /\ u > 0
  /\ u >= v
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "Loop"

Terminate ==
  /\ pc = "Loop"
  /\ u = 0
  /\ UNCHANGED << u, v >>
  /\ pc' = "Done"

StutterDone ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  Swap \/ Sub \/ Terminate \/ StutterDone

Spec ==
  /\ Init
  /\ [][Next]_vars

=============================================================================