---- MODULE Counter ----
EXTENDS Naturals

CONSTANT UpperBound

ASSUME UpperBound \in Nat \ {0}

VARIABLE x

vars == << x >>

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

\* Invariant: x always remains strictly below UpperBound
Inv == x < UpperBound

\* State constraint for model checking: bounds the explored state space
Constraint == x < UpperBound

TypeOK == x \in Nat

====