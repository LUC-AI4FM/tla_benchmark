```
MODULE SmallTemporalSystem
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 0)

F(var) == (var \in 0..9) /\ (var mod 2 = 0)

Next == \A s' \in [s : {0,1,2,3,4,5,6,7,8,9}] : F(s')

Spec == Init /\ [][Next]_s

THEOREM Spec => []F(s)
```