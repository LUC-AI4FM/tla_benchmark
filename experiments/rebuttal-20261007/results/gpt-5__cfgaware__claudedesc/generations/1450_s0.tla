---- MODULE RandomSubsetPerfTest ----
EXTENDS Randomization

VARIABLES x

S == 1..9
T == 1..10
FuncSpace == [S -> T]

Init == x = RandomSubset(FuncSpace, 1000)

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

====