MODULE SmallFactorial

VARIABLES x

fact == \lambda n : IF n = 0 THEN 1 ELSE n * fact(n-1)

Init == x = 0

A == /\ x' = fact(3)
B == /\ x' = fact(9)

StutterX == /\ x' = x

Next == A \/ B \/ StutterX

Spec == Init /\ []Next
