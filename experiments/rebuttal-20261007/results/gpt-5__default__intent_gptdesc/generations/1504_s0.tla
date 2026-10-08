------------------------------ MODULE ConstantTrueSystem ------------------------------

EXTENDS TLC

CONSTANTS Dummy

VARIABLES b

Init ==
  b = TRUE

Next ==
  UNCHANGED b

Spec ==
  Init /\ [][Next]_b

(*
  Safety invariants
*)
AlwaysTrue ==
  [](b = TRUE)

OnlyStuttering ==
  [](UNCHANGED b)

(*
  Liveness (no deadlock): Next is always enabled in every reachable state
*)
NoDeadlock ==
  [](ENABLED Next)

=============================================================================