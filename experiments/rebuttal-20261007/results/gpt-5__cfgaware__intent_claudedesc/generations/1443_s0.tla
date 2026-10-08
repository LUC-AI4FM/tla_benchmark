----------------------------- MODULE CounterPossible -----------------------------

EXTENDS Naturals, TLC

VARIABLE x

(*
  Simple cyclic counter over {0,1,2}
*)

Init ==
  x = 0

Next ==
  x' = IF x = 2 THEN 0 ELSE x + 1

(*
  Predicates of interest
*)
HitTwo ==
  x = 2

HitOne ==
  x = 1

Wrap ==
  /\ x = 2
  /\ x' = 0

(*
  TLC's _POSSIBLE directive (stubbed here so SANY parses). TLC recognizes and
  instruments calls to _POSSIBLE during model checking.
*)
_POSSIBLE(name, p) == p

(*
  Register the three predicates for POSSIBLE-tracking.
  TLC should record whether each is ever satisfied along explored behaviors.
*)
PossibleChecks ==
  /\ _POSSIBLE("HitTwo", HitTwo)
  /\ _POSSIBLE("HitOne", HitOne)
  /\ _POSSIBLE("Wrap", Wrap)

(*
  Behavior spec
*)
Spec ==
  Init /\ [][Next]_x

(*
  Postcondition asserting TLC recorded exactly one witness per predicate.
  TLCGet is provided by the TLC module; the specific keys are interpreted by TLC.
*)
PostCondition ==
  /\ TLCGet("POSSIBLE!HitTwo") = 1
  /\ TLCGet("POSSIBLE!HitOne") = 1
  /\ TLCGet("POSSIBLE!Wrap") = 1

=============================================================================