```
MODULE Wrapper
VARIABLE x

Spec == x = 0 /\ [][Next]_x

Next == (x' = (x + 1) % 3)

AllDone == x = 2
AtOne == x = 1
WrapAround == x = 2 /\ x' = 0

THEOREM Spec => <>AllDone
THEOREM Spec => <>AtOne
THEOREM Spec => <>WrapAround

PossibilityTracking == 
  "_POSSIBLE" -> {"AllDone", "AtOne", "WrapAround"}

PossibleCounts ==
  LET namedStats == TLCGet("all:named") IN
  /\ namedStats["AllDone"] = 1
  /\ namedStats["AtOne"] = 1
  /\ namedStats["WrapAround"] = 1

=============================================================================
```
Note: The `THEOREM` statements are not strictly necessary for the specification but can help TLC to verify additional properties of the system. The `PossibilityTracking` and `PossibleCounts` definitions serve to configure TLC's possibility tracking mechanism and postcondition, respectively.