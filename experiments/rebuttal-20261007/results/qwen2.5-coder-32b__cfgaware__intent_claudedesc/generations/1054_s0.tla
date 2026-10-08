------------------------------- MODULE DijkstraTokenRing -------------------------------

CONSTANTS N, M

VARIABLES counters

ASSUME N \in Nat /\ M \in Nat /\ N <= M + 1

Init == counters \in [0..N-1 -> 0..M]

Next ==
    \/ \E i \in 0..N-1 : 
        LET pred_i == (i - 1) % N
            succ_i == (i + 1) % N
        IN /\ counters' = [counters EXCEPT ![i] = IF i = 0 /\ counters[i] = counters[pred_i]
                                      THEN (counters[i] + 1) % M
                                      ELSE IF counters[i] # counters[pred_i]
                                           THEN counters[pred_i]
                                           ELSE counters[i]]
           /\ \A j \in 0..N-1 : j # i => counters'[j] = counters[j]

Spec == Init /\ [][Next]_<<counters>>

TokenInvariant ==
    \E i \in 0..N-1 :
        LET pred_i == (i - 1) % N
            succ_i == (i + 1) % N
        IN /\ counters[i] = counters[pred_i]
           /\ \A j \in 0..pred_i : counters[j] = counters[0]
           /\ \A j \in succ_i..N-1 : counters[j] = counters[pred_i]

WF == WF_next(<<counters>>)

THEOREM Spec => <>[](TokenInvariant) 
    <== <<WF>>

=============================================================================