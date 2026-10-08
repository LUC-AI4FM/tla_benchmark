```
MODULE BoolSM

VARIABLE x

Switch(v) == ~v

A == x' = Switch(x)
B == x' = Switch(x)

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_x
```