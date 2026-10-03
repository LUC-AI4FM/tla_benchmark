```
MODULE Spec
VARIABLE x

fact(n) == IF n = 0 THEN 1 ELSE n * fact(n-1)

A == x' = fact(3)
B == x' = fact(9)
Next == A \/ B

Spec == x = 0 /\ [][Next]_x
```