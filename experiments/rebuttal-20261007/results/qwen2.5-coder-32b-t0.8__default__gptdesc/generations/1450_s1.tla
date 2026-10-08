------------------------------- MODULE RandomFunctionSampler -------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS S, T

VARIABLE x

Init == /\ S = {1, 2, 3, 4, 5, 6, 7, 8, 9}
        /\ T = 1..10
        /\ x \in RandomSubset(1000, [S -> T])

Next == TRUE

Spec == /\ Init
        /\ [][Next]_<<x>>
        /\ WF_next(<<x>>)

Inv == TRUE

================================================================================