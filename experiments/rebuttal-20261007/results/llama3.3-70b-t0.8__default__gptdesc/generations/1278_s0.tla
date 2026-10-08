```
MODULE SmallTemporalSystem
EXTENDS Integers

CONSTANTS

VARIABLES s

Init == s = 0

F(var) == var \in (0..9) /\ var % 2 = 0

Next == \A s' \in (0..9) : F(s')

Spec == Init /\ [][Next]_s

THEOREM Spec => []F(s)
```