------------------------------- MODULE TokenRing -------------------------------

CONSTANTS N, M

ASSUME N \in Nat \ {0}
ASSUME M \in Nat \ {0}

VARIABLES counters

Init == /\ counters \in [1..N -> 0..M-1]

Next ==
    \/ \E i \in 1..N : 
        /\ counters' = [counters EXCEPT ![i] = (counters[i] + 1) % M]
        /\ i = 1
    \/ \E i \in 1..N :
        /\ counters'[i] = counters[(i - 1) % N + 1]
        /\ counters' = [EXCEPT ![(i - 1) % N + 1] = counters[(i - 1) % N + 1]]
        /\ i \in 2..N

Spec == Init /\ [][Next]_<<counters>>

Safety ==
    [](\A i \in 1..N : counters[i] \in 0..M-1)

UniqueToken ==
    \E v \in 0..M-1 :
        \E boundary \in 1..N :
            (\A i \in 1..boundary-1 : counters[i] = v) /\
            (\A i \in boundary+1..N : counters[i] = (v - 1) % M)

Stabilization ==
    <>(UniqueToken /\ []<>UniqueToken)

WF == WF_next(Next, <<counters>>)

FairSpec == Spec /\ WF

THEOREM FairSpec => Safety
THEOREM FairSpec => Stabilization

=============================================================================