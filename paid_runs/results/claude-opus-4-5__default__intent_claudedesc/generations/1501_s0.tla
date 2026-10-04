---------------------------- MODULE RecursiveFactorial ----------------------------
EXTENDS Naturals

CONSTANTS Input1, Input2

VARIABLES result

RECURSIVE Factorial(_)

Factorial(n) ==
    IF n <= 0
    THEN 1
    ELSE n * Factorial(n - 1)

Init == result = 0

ComputeFactorial1 == result' = Factorial(Input1)

ComputeFactorial2 == result' = Factorial(Input2)

Next == ComputeFactorial1 \/ ComputeFactorial2

Spec == Init /\ [][Next]_result

===================================================================================