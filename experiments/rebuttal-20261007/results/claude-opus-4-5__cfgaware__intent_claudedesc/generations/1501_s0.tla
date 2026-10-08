---------------------------- MODULE RecursiveFactorial ----------------------------
EXTENDS Naturals

VARIABLES x

RECURSIVE Factorial(_)

Factorial(n) ==
    IF n = 0 THEN 1
    ELSE n * Factorial(n - 1)

Init == x = 0

Step1 == x' = Factorial(3)

Step2 == x' = Factorial(5)

Next == Step1 \/ Step2

Spec == Init /\ [][Next]_x

===================================================================================