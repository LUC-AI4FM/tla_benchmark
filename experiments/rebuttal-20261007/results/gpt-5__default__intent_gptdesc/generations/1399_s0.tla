------------------------------ MODULE Toggle ------------------------------

EXTENDS TLC

CONSTANTS Unused

VARIABLES x

Init ==
  x = TRUE

Flip ==
  x' = ~x

Stutter ==
  UNCHANGED x

Next ==
  Flip \/ Stutter

Spec ==
  Init /\ [][Next]_x

(*
 Safety properties
*)
TypeOK ==
  x \in BOOLEAN

AlwaysBoolean ==
  [](x \in BOOLEAN)

NoIllegalValues ==
  [](x = TRUE \/ x = FALSE)

(*
 Liveness / non-deadlock properties
*)
AlwaysEnabled ==
  [](ENABLED Flip \/ ENABLED UNCHANGED x)

AlwaysEnabledAll ==
  [](ENABLED [Next]_x)

(*
 Comparative invariant claims
*)
StrongAlwaysTrue ==
  [](x = TRUE)

WeakerObservational ==
  [](x \in BOOLEAN)

============================================================================