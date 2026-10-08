MODULE SmallFactorial
EXTENDS Naturals, Temporal

VARIABLES x

fact == [n \in Nat |-> IF n = 0 THEN 1 ELSE n * fact[n-1]]

Init == x = 0

A == x' = fact[3]
B == x' = fact[9]

Next == A \/ B

Spec == Init /\ [] (Next \/ Stutter)

END