----------------------------- MODULE PossibleCoverageTest -----------------------------
EXTENDS Naturals, TLC

VARIABLES x

Init == x = 0

Next == x' = IF x = 2 THEN 0 ELSE x + 1

AllDone == x = 2

AtOne == x = 1

WrapAround == /\ x = 2
              /\ x' = 0

Spec == Init /\ [][Next]_x

PossibleCounts ==
  LET named == TLCGet("all:named")
  IN /\ Assert(named["AllDone"] = 1, "AllDone possibility count should be 1")
     /\ Assert(named["AtOne"] = 1, "AtOne possibility count should be 1")
     /\ Assert(named["WrapAround"] = 1, "WrapAround possibility count should be 1")

=============================================================================