```
MODULE SmallTemporalSystem
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 0)

F(var) == (var \in 0..9) /\ (var mod 2 = 0)

Next == \A s' \in [s : {x \in 0..9 : F(x)}] : 
        (s' = s) \/ F(s')

Spec == Init /\ [][Next]_s

THEOREM Spec => []F(s)
```