------------------------------- MODULE TokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M
ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 1

VARIABLES counters

Init == /\ counters \in [1..N -> {0..M-1}]
        /\ \/ \E i \in 1..N : counters[i] # (counters[<<i+1>>_mod N] - 1) % M
           \/ \A i \in 1..N : counters[i] = counters[<<i+1>>_mod N]

Next == \/ /\ \E i \in 1..N : counters' = [counters EXCEPT ![i] = (counters[i] + 1) % M]
             /\ \A j \in 1..N \ {i} : counters'[j] = counters[j]
        \/ /\ \E i \in 1..N : counters[i] # counters[<<i-1>>_mod N]
             /\ counters' = [counters EXCEPT ![i] = counters[<<i-1>>_mod N]]
             /\ \A j \in 1..N \ {i} : counters'[j] = counters[j]

Spec == Init /\ [][Next]_<<counters>>

Safety == \A i \in 1..N : counters[i] \in {0..M-1}

UniqueToken ==
    \E v \in {0..M-1}, i \in 1..N :
        (\A j \in 1..i-1 : counters[j] = v)
        /\ (\A j \in i..N : counters[j] = (v - 1) % M)

Stabilization == <>[](UniqueToken)

WF_Increment ==
    WF_<<\E i \in 1..N : counters' = [counters EXCEPT ![i] = (counters[i] + 1) % M]
             /\ \A j \in 1..N \ {i} : counters'[j] = counters[j]>>_<<counters>>

WF_Copy ==
    WF_<<\E i \in 1..N : counters[i] # counters[<<i-1>>_mod N]
             /\ counters' = [counters EXCEPT ![i] = counters[<<i-1>>_mod N]]
             /\ \A j \in 1..N \ {i} : counters'[j] = counters[j]>>_<<counters>>

Fairness == WF_Increment /\ WF_Copy

CompleteSpec == Spec /\ Safety /\ Stabilization /\ Fairness
=============================================================================