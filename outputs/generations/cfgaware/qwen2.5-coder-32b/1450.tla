------------------------------- MODULE RandomSubsetSampler -------------------------------

CONSTANTS S, T

VARIABLE x

ASSUME S = {1..9}
ASSUME T = 1..10

Init == x \in RandomSubset(1000, [S -> T])

Next == TRUE

Spec == Init /\ [](Next)

Inv == TRUE

=============================================================================