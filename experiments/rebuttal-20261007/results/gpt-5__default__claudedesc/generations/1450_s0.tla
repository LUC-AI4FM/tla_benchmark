---- MODULE RandomSubsetHugeFunctionSpaceTest ----
EXTENDS Integers, Randomization

CONSTANTS K
ASSUME K = 1000

VARIABLES x

S == 1..9
T == 1..10

Init == x = RandomSubset([S -> T], K)

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

====