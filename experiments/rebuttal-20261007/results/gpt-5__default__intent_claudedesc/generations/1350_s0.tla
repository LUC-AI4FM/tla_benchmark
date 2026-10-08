---- MODULE CounterUpToFive ----
EXTENDS Naturals, Integers

CONSTANTS Max
ASSUME Max = 5

VARIABLES counter

Vars == << counter >>

Init ==
  counter = 1

Inc ==
  /\ counter < Max
  /\ counter' = counter + 1

Stop ==
  /\ counter = Max
  /\ UNCHANGED counter

Next ==
  Inc \/ Stop

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Inc)

(*
  Safety invariants
*)
TypeInv ==
  counter \in 1..Max

(*
  Liveness properties
  - Stabilizes: eventually, the counter is permanently 5.
  - LeadsToStable: from the initial state (counter = 1), the system eventually stabilizes at 5.
*)
Stabilizes ==
  <>[] (counter = Max)

LeadsToStable ==
  (counter = 1) ~> [] (counter = Max)
=============================