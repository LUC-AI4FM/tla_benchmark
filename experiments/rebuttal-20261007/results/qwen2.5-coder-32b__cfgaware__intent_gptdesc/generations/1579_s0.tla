------------------------------- MODULE TokenRing -------------------------------

CONSTANTS N, K

ASSUME N > 0 /\ K > N

VARIABLES counters

Init == 
    /\ counters \in [0..N-1 -> 0..K-1]

Next ==
    \/ \E i \in 0..N-1 : 
        (i = 0 /\ counters' = [counters EXCEPT ![i] = (counters[i] + 1) % K])
    \/ \E i \in 0..N-1 :
        (i > 0 /\ counters'[i] = counters[(i - 1) % N])

Spec ==
    Init /\ [][Next]_<<counters>>

SomeoneHoldsToken ==
    \E i \in 0..N-1 : counters[i] # counters[(i - 1) % N]

EventuallyJustOneHoldsToken ==
    <>[] (\A i, j \in 0..N-1 : (i = j \/ counters[i] = counters[j]))

=============================================================================