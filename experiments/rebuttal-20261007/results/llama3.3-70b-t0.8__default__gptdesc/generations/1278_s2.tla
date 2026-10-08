```
MODULE SmallTemporalSystem
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 0)

F(var) == (var >= 0) /\
           (var <= 9) /\
           ((var mod 2) = 0)

Next == [](F(s'))_s

Spec == Init /\ [][Next]_s

THEOREM Spec => []Init
```