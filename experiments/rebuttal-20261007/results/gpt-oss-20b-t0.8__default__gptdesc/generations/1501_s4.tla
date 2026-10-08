------------------------------ MODULE FactorialSM ------------------------------

EXTENDS Naturals

VARIABLE x

RECURSIVE fact/1

fact(n) ==
    IF n = 0 THEN
        1
    ELSE
        n * fact(n - 1)

A == x' = fact(3)
B == x' = fact(9)
Next == A \/ B
Stutter == x' = x

Init == x = 0

Spec == Init /\ [] (Next \/ Stutter)

=============================================================================