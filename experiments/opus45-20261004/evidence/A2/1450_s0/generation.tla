---------------------------- MODULE RandomSubsetTest ----------------------------
EXTENDS Integers, Randomization

CONSTANTS S, T

VARIABLES x

Init == x = RandomSubset(1000, [S -> T])

Next == x' = x

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

================================================================================