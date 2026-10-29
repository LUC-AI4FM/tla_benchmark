---------------------------- MODULE SmallMachine ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x

vars == << x >>

\* Every subset of S has nonnegative cardinality
Op1(S) == \A T \in SUBSET S : Cardinality(T) >= 0

\* The maximum element of the interval 1..n, chosen via CHOOSE
Op2(n) == CHOOSE m \in 1..n : \A k \in 1..n : k <= m

TypeOK == x \in Nat

Init == /\ x = 0
        /\ Op1(1..17)

A(n) == x' = Op2(n)

B(n) == x' = Op2(n)

Next == A(10) \/ B(3)

Spec == Init /\ [][Next]_vars

=============================================================================