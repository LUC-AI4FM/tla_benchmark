---- MODULE A ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Op1(S) == \A T \in SUBSET S : Cardinality(T) >= 0

Op2(n) == CHOOSE v \in 1..n : \A w \in 1..n : w /= v => v > w

A(n) == x' = Op2(n)

B(n) == x' = Op2(n)

Init == /\ x = 0
        /\ Op1(1..17)

Next == A(10) \/ B(3)

Spec == Init /\ [][Next]_x

====