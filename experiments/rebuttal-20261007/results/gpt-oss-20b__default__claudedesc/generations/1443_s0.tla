------------------------------ MODULE CounterPossibilityTest ------------------------------
EXTENDS Integers
VARIABLES x

-- _POSSIBLE := {AllDone, AtOne, WrapAround}

Init == x = 0

Next == x' = Mod(x + 1, 3)

vars == <<x>>

Spec == Init /\ [][Next]_vars

AllDone    == x = 2
AtOne      == x = 1
WrapAround == x = 2 /\ x' = 0

PostCondition ==
  LET stats == TLCGet("all:named") IN
    /\ stats["AllDone"]     = 1
    /\ stats["AtOne"]       = 1
    /\ stats["WrapAround"]  = 1

=============================================================================