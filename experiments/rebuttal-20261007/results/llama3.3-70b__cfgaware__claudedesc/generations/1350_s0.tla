```
MODULE Github1037
VARIABLE x

Init == (x = 1)

Next == IF x < 5 THEN x' = x + 1 ELSE x' = x

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Liveness == (x = 1) => <>[](x = 5)
```
Note: The `WF_x(Next)` operator is used to express weak fairness, which ensures that if `Next` is continuously enabled, it will eventually be taken. This is a built-in operator in TLA+ and does not need to be defined separately.