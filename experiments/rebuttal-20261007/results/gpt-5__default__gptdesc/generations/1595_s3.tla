--------------------------- MODULE FairSequentialCounter ---------------------------

EXTENDS Naturals, TLC

CONSTANT N
ASSUME N = 10

VARIABLES x, pc

vars == << x, pc >>

(*
  Initialization: x starts at 0, control at "Loop"
*)
Init ==
  /\ x = 0
  /\ pc = "Loop"

(*
  Main loop step: while x < N, increment x and stay in "Loop"
*)
Inc ==
  /\ pc = "Loop"
  /\ x < N
  /\ x' = x + 1
  /\ pc' = "Loop"

(*
  Exit to terminal state when the loop condition is false
*)
Exit ==
  /\ pc = "Loop"
  /\ x >= N
  /\ x' = x
  /\ pc' = "Done"

Next == Inc \/ Exit

(*
  Standard temporal behavior with weak fairness on Next
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
  Safety (state) invariants
*)
TypeOK == /\ x \in Nat /\ pc \in {"Loop", "Done"}
Inv == /\ x \in 0..N /\ pc \in {"Loop", "Done"}

(*
  Liveness: termination property
*)
Termination == <> (pc = "Done")

(*
  Auxiliary predicates
*)
AtFive == x = 5
FinishLoop == /\ pc = "Loop" /\ x >= N

(*
  TLC-based check: possible counter values
*)
PossibleCounts == 0..N

=============================================================================