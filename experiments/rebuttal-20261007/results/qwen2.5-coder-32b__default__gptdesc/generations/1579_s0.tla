------------------------------- MODULE DijkstraTokenRing -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, K
ASSUME K > N /\ N > 0

VARIABLES values

Init == 
    /\ values \in [0..N-1 -> 0..K-1]
    /\ (\E i \in 0..N-1 : values[i] = values[(i-1) % N])

Next ==
    \/ /\ values' = [values EXCEPT ![0] = (IF values[0] = values[N-1] THEN (values[0] + 1) % K ELSE values[0])]
       /\ \A i \in 1..N-1 : values'[i] = (IF values[i] /= values[(i-1) % N] THEN values[(i-1) % N] ELSE values[i])
    \/ /\ values' = [values EXCEPT ![0] = values[0]]
       /\ \A i \in 1..N-1 : values'[i] = (IF values[i] /= values[(i-1) % N] THEN values[(i-1) % N] ELSE values[i])

WF == WF_(Next, << >>)

Spec ==
    /\ Init
    /\ [][Next]_<< >>
    /\ WF

TokenExists ==
    \E i \in 0..N-1 : values[i] /= values[(i-1) % N]

SingleToken ==
    \A i \in 0..N-1, j \in 0..N-1 : i # j => values[i] = values[(i-1) % N] \/ values[j] = values[(j-1) % N]

Inv == TokenExists /\ SingleToken

THEOREM Spec => []Inv
=============================================================================