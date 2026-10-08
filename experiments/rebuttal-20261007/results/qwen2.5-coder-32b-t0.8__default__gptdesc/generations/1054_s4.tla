```tla
MODULE DijkstraTokenRing

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M

VARIABLES counters

Init == /\ counters \in [0..N-1 -> 0..M-1]
        /\ \A i \in 1..N-1 : counters[i] = counters[i-1]

Next ==
    \/ /\ counters[0]' = (counters[N-1] + 1) \% M
       /\ \A i \in 1..N-1 : counters'[i] = counters[i]
    \/ \E j \in 1..N-1 :
        /\ counters[j] # counters[(j-1) % N]
        /\ counters'[j] = counters[(j-1) % N]
        /\ \A i \in (1..N-1) \ {j} : counters'[i] = counters[i]

Stabilization ==
    \E v \in 0..M-1 :
        \A j \in 1..N-1 :
            counters[j] = (v + j) \% M

Spec == Init /\ [][Next]_<<counters>> /\ <>(Stabilization)_<<counters>>

WF_STABILIZATION == WF_next(Stabilization, <<counters>>)

CONSTRAINTS
    N \geq 1
    M \geq 1
    N \leq M + 1

====

```