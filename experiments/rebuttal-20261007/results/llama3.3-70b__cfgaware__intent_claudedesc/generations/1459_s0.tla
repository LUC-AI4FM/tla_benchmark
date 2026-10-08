```
MODULE CounterDemo
VARIABLE counter

Constant Limit == 3

Init == (counter = 0)

Next == IF counter < Limit THEN counter' = counter + 1 ELSE counter' = counter

Spec == Init /\ [][Next]_counter
```