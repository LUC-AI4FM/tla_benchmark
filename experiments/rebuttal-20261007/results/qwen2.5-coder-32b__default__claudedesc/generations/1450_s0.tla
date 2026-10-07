------------------------------- MODULE RandomizationTest -------------------------------
EXTENDS Integers, FiniteSets, TLC, Randomization

CONSTANTS S, T
VARIABLE x

ASSUME Cardinality(S) = 9 /\ Cardinality(T) = 10

Init == x \in RandomSubset([S -> T], 1000)

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Invariant == TRUE

=============================================================================