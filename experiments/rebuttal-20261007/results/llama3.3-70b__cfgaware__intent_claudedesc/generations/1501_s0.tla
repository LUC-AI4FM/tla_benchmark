```
MODULE DemoRecursiveOperator
VARIABLE x

RECURSIVE Factorial(_)
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n-1)

Init == x = 0

Next == (x' = Factorial(3)) \/ (x' = Factorial(5))

Spec == Init /\ [][Next]_
```
Note: The `_` at the end of `Next`_ in the `Spec` definition is necessary to indicate that `Next` is a state predicate, which is a common convention in TLA+.