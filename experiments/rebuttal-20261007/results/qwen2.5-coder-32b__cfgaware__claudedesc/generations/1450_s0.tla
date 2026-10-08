------------------------------- MODULE RandomFunctionSetTest -------------------------------

CONSTANTS S, T

VARIABLE x

S == {1, 2, 3, 4, 5, 6, 7, 8, 9}
T == 1..10

Init == x \in RandomSubset([S -> T], 1000)

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Invariants == TRUE

=============================================================================