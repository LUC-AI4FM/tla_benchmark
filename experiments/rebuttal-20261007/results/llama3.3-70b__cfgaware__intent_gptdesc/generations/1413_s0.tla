---------------------------- MODULE ImmutableTautologyDetector ----------------------------
EXTENDS Integers, TLC

CONSTANT AlwaysTrue

VARIABLE state

Init == state = AlwaysTrue

NextState(st) == st = state

Spec == Init /\ [][NextState(state)]_state

Theorem == [](AlwaysTrue => <>[]AlwaysTrue)
=============================================================================