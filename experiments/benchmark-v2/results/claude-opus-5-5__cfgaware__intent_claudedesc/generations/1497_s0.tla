---- MODULE ChooseMax ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Max(S) == CHOOSE m \in S : \A n \in S : n # m => m > n

CardinalityCheck(S) == \A T \in SUBSET S : Cardinality(T) >= 0

Init == /\ x = 0
        /\ CardinalityCheck(1..3)

Next == \/ x' = Max(1..10)
        \/ x' = Max(1..3)

Spec == Init /\ [][Next]_x
====