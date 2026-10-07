```
MODULE StaticSystem
EXTENDS Integers

VARIABLE x

Init == (x = 0)

Next ==[][UNCHANGED x]_x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
```