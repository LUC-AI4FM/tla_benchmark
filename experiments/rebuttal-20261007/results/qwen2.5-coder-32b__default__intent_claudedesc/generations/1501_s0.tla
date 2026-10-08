------------------------------- MODULE RecursiveFactorial -------------------------------

EXTENDS Naturals, TLC

CONSTANTS Input1, Input2

VARIABLES x

RECURSIVE Factorial(_)

Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

Init == x = 0

Next ==
    \/ /\ x' = Factorial(Input1)
       /\ UNCHANGED <<>>
    \/ /\ x' = Factorial(Input2)
       /\ UNCHANGED <<>>

Spec == Init /\ [][Next]_<<x>>

=============================================================================