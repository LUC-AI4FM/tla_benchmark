------------------------------- MODULE RandomSubsetSampler -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS S, T
VARIABLE x

ASSUME Cardinality(S) = 9 /\ T = {1..10}

Init == x \in RandomSubset(1000, [S -> T])

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

=============================================================================