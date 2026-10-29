---- MODULE A ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Op1(S) == \A T \in SUBSET S : Cardinality(T) >= 0

Op2(n) == CHOOSE i \in 1..n : \A j \in 1..n : (j # i) => (i > j)

Init == /\ x = 0
        /\ Op1(1..17)

A(n) == x' = Op2(n)

B(n) == x' = Op2(n)

Next == A(10) \/ B(3)

====