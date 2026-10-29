---- MODULE ChooseMax ----
EXTENDS Naturals, FiniteSets

VARIABLE x

vars == << x >>

\* Maximum of a set: the unique element strictly greater than all others
Max(S) == CHOOSE m \in S : \A n \in S \ {m} : m > n

\* Sanity check: every subset of a finite set has non-negative cardinality
SubsetCardinalityOK(S) == \A T \in SUBSET S : Cardinality(T) >= 0

Init ==
    /\ SubsetCardinalityOK(1..3)
    /\ x = 0

Next ==
    \/ x' = Max(1..10)
    \/ x' = Max(1..3)

Spec == Init /\ [][Next]_vars

TypeOK == x \in {0, 3, 10}

====