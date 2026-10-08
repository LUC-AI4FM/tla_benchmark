```tla
MODULE DijkstraTokenRing

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS N, K
ASSUME K > N /\ N > 0

VARIABLES values

Init == /\ values \in [0..N-1 -> 0..K-1]
      /\ (\E i \in 0..N-1 : values[i] = 0)

Next ==
    LET next_values == [i \in 0..N-1 |-> 
                            IF i = 0 THEN
                                IF values[0] = values[N-1] THEN (values[0] + 1) % K ELSE values[0]
                            ELSE
                                IF values[i] =/= values[(i - 1) % N] THEN values[(i - 1) % N] ELSE values[i]
                        ]
    IN /\ UNCHANGED <<>>
       /\ values' = next_values

Spec ==
    Init /\ [][Next]_<<values>>

WF == WF_next(<<>>, _)

TypeOK ==
    /\ values \in [0..N-1 -> 0..K-1]

TokenExists ==
    \E i \in 0..N-1 : values[i] = (values[(i - 1) % N] + 1) % K

SingleToken ==
    \A i, j \in 0..N-1 : i # j => \/ values[i] # (values[(i - 1) % N] + 1) % K
                                \/ values[j] =/= (values[(j - 1) % N] + 1) % K

SpecWithProperties ==
    Spec /\ WF /\ TypeOK /\ TokenExists /\ <>[]SingleToken
```