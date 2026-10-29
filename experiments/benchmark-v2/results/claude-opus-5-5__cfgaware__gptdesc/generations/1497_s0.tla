---- MODULE Spec ----
EXTENDS Naturals, FiniteSets

VARIABLE x

vars == <<x>>

Op1(S) == \A T \in SUBSET S : Cardinality(T) >= 0

Op2(n) == CHOOSE m \in 1..n : \A k \in 1..n : k <= m

Init == /\ x = 0
        /\ Op1(1..17)

A(n) == x' = Op2(n)

B(n) == x' = Op2(n)

Next == A(10) \/ B(3)

====