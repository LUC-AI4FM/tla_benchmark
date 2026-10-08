```
MODULE CounterDemo
EXTENDS Integers

CONSTANTS Bound
VARIABLES counter

Init == (counter = 0)

Next == IF counter < Bound THEN counter' = counter + 1 ELSE counter' = counter

Spec == Init /\ [][Next]_counter

THEOREM Spec => []Init
```
Note: The above TLA+ module uses the `Integers` module which is a standard module in TLA+ that provides integer operators and constants. 

Also, note that this specification does not explicitly include fairness conditions as there was no mention of them in the system description provided. If fairness conditions were required, they would typically be added using the `WF_vars` (weak fairness) or `SF_vars` (strong fairness) operators.