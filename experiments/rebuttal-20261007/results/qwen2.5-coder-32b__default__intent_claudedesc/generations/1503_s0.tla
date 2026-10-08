------------------------------- MODULE HigherOrderFilter -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS 
    \* No constants needed for this example

VARIABLES x

SetFilter(S, UnaryPred, BinaryPred) == { e \in S : UnaryPred(e) /\ BinaryPred(e, TRUE) }

Init == x = CHOOSE y \in SetFilter({1, 2, 3, 4, 5}, (e \in Int => e > 1), (e \in Int, b \in BOOLEAN => e % 2 # 0))

Next == /\ UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================