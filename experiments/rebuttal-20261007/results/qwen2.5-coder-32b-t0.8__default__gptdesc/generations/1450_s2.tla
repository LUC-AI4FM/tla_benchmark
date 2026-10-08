---------------------------- MODULE SamplingSystem ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS S

VARIABLE x

ASSUME Cardinality(S) = 9

Init == x \in RandomSubset(1000, [S -> (1..10)])

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

=============================================================================