------------------------------ MODULE FactorialSM ------------------------------
IMPORTING Integers

Nat == {n \in Int : n >= 0}

VARIABLE x

fact == [n \in Nat |-> IF n = 0 THEN 1 ELSE n * fact[n-1]]

A == x' = fact[3]
B == x' = fact[9]

Next == A \/ B
Init == x = 0

Spec == Init /\ [] [Next]_<<x>>

=============================================================================