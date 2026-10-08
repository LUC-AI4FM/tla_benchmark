```
MODULE RecursiveFactorial
EXTENDS Integers

CONSTANTS Input1, Input2

VARIABLES var

RECURSIVE Factorial(_)
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n-1)

Init == var = 0

Next == \/ (var' = Factorial(Input1))
          \/ (var' = Factorial(Input2))

Spec == Init /\ [][Next]_var
```
Note: The `Input1` and `Input2` constants should be replaced with the actual values for which you want to compute the factorial.