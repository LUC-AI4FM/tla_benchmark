```
MODULE Clock
EXTENDS Integers

CONSTANTS None

VARIABLES hour

Init == (hour \in 1..12)

Next == (* stuttering step or advance hour *)
          \/ hour' = hour
          \/ (hour' = IF hour = 12 THEN 1 ELSE hour + 1)

Spec == Init /\ [][Next]_hour

THEOREM Spec => []Init
```