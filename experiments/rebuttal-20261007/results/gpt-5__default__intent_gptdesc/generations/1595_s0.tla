------------------------------ MODULE LoopWithFairness ------------------------------

EXTENDS Naturals

CONSTANT BOUND
ASSUME BOUND \in Nat /\ BOUND = 10

VARIABLES cnt, terminated

vars == << cnt, terminated >>

Init ==
  /\ cnt = 0
  /\ terminated = FALSE

Inc ==
  /\ ~terminated
  /\ cnt < BOUND
  /\ cnt' = cnt + 1
  /\ UNCHANGED terminated

Terminate ==
  /\ ~terminated
  /\ cnt >= BOUND
  /\ terminated' = TRUE
  /\ UNCHANGED cnt

Idle ==
  /\ terminated
  /\ UNCHANGED vars

Next == Inc \/ Terminate \/ Idle

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Inc)
  /\ WF_vars(Terminate)

(*
  Safety invariants and properties to verify
*)
SafetyInv ==
  /\ cnt \in 0..BOUND
  /\ terminated \in BOOLEAN

Safety_NeverDecreases ==
  [] (cnt' >= cnt)

Safety_NoSkip ==
  [] (cnt' = cnt \/ cnt' = cnt + 1)

StableAfterTermination ==
  [] (terminated => /\ terminated' /\ cnt' = cnt)

(*
  Liveness/progress properties
*)
TerminationProgress ==
  <> terminated

Reach5_Possible ==
  <> (cnt = 5)

PenultimateToFinal_Possible ==
  <> (/\ cnt = BOUND - 1 /\ cnt' = BOUND)

=============================================================================