----------------------------- MODULE ToggleBoolean -----------------------------

EXTENDS TLC

CONSTANTS NoConst

VARIABLES b

Init == b = TRUE

Next == b' = ~b

Spec == Init /\ []Next

(*
  Properties for checking with TLC:
  - InvAlwaysTrue: state invariant that is intentionally violated by the toggling behavior.
  - StatePred_EqualsTrue: same state predicate form for experimentation.
  - BareVarProperty: exposes the variable directly as a state predicate.
  - AlwaysTrue: temporal property asserting b is always TRUE (violated).
  - TrivialAlways: a trivially true temporal property.
*)

InvAlwaysTrue == b = TRUE

StatePred_EqualsTrue == b = TRUE

BareVarProperty == b

AlwaysTrue == [](b = TRUE)

TrivialAlways == []TRUE

=============================================================================