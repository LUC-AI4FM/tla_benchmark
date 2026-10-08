------------------------------- MODULE TokenRing -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, M
ASSUME N \in Nat /\ M \in Nat /\ N >= 1 /\ M >= 1 /\ N <= M + 1

VARIABLES counters

Init == 
    /\ counters \in [0..N-1 -> 0..M-1]
    /\ (\E i \in 0..N-1: counters[i] = 0)

Next ==
    \/ /\ counters[0]' = (counters[N-1] + 1) \% M
       /\ \A j \in 1..N-1: counters[j]' = counters[j]
    \/ \E i \in 1..N-1:
        /\ counters[i] /= counters[(i-1)%N]
        /\ counters' = [counters EXCEPT ![i] = counters[(i-1)%N]]
       /\ \A j \in (1..N-1) \ {i}: counters[j]' = counters[j]

Spec == 
    Init /\ [][Next]_<<counters>>

Stabilization ==
    \E tokenValue \in 0..M-1:
        \A i \in 0..N-1: <>[][counters[i] = tokenValue][]

Fairness ==
    WF_next(<<counters>>)

=============================================================================