--------------------------- MODULE FactorialSM ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

Fact == [n \in Nat |-> IF n = 0 THEN 1 ELSE n * Fact[n-1]]

Init   == x = 0
A      == x' = Fact[3]
B      == x' = Fact[9]
Next   == A \/ B

Stutter == (\A x': x' = x)

TypeInv == x \in Nat

Spec == Init /\ [] ( Next \/ Stutter ) /\ [] TypeInv

=============================================================================