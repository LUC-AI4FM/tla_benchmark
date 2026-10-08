```
MODULE Counter
EXTENDS Integers

CONSTANTS None

VARIABLES counter

Init == (counter = 1)

Next == IF counter < 5 THEN counter' = counter + 1 ELSE counter' = counter

Spec == Init /\ [][Next]_counter

THEOREM Spec => <>[]counter = 5
WF_Vars == <<counter>>

Fairness == WF_vars(Next, WF_Vars)
```
Note: The above TLA+ specification uses the "leads to stable" pattern and weak fairness to ensure that if the counter starts at 1, it will eventually stabilize permanently at 5.