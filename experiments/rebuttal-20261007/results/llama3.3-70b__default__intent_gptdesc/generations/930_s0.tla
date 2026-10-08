```
MODULE Clock
EXTENDS Integers

CONSTANTS None

VARIABLES hour

Init == hour \in 1..12

Next == hour' = IF hour = 12 THEN 1 ELSE hour + 1

Spec == Init /\ [][Next]_hour

THEOREM Spec => []Init
THEOREM Spec => <>hour = 1
THEOREM Spec => <>hour = 2
THEOREM Spec => <>hour = 3
THEOREM Spec => <>hour = 4
THEOREM Spec => <>hour = 5
THEOREM Spec => <>hour = 6
THEOREM Spec => <>hour = 7
THEOREM Spec => <>hour = 8
THEOREM Spec => <>hour = 9
THEOREM Spec => <>hour = 10
THEOREM Spec => <>hour = 11
THEOREM Spec => <>hour = 12

Fairness == WF_vars(Next, hour)

THEOREM Spec => Fairness
```