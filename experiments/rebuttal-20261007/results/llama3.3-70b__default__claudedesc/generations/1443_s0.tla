```
MODULE Wrapper
EXTENDS Integers
CONSTANTS 
VARIABLES x

Init == (x = 0)

Next == (x' = (x + 1) % 3)

Spec == Init /\ [][Next]_x

AllDone == (x = 2)
AtOne == (x = 1)
WrapAround == (x = 2) /\ (x' = 0)

THEOREM Spec => []<>(AllDone)
THEOREM Spec => []<>(AtOne)
THEOREM Spec => <>[](WrapAround => (x' = 0))

PossibleCounts ==
  LET named == TLCGet("all:named") IN
  /\ named["AllDone"] = 1
  /\ named["AtOne"] = 1
  /\ named["WrapAround"] = 1

THEOREM Spec => <>(PossibleCounts)
```