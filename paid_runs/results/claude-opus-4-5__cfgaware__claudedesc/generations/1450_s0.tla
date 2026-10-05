---------------------------- MODULE Randomization1 ----------------------------
EXTENDS Integers, Randomization

VARIABLES x

S == 1..9
T == 1..10

Init == x \in RandomSubset(1000, [S -> T])

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

================================================================================