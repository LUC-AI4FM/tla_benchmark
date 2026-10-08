------------------------------- MODULE DijkstraTokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M
ASSUME N \in 1..M+1 /\ M \in Nat

VARIABLES counters

Init == /\ counters \in [0..N-1 -> 0..M]
      /\ \/ \E i \in 0..N-2 : counters[i] # counters[i+1]
         \/ counters[N-1] # counters[0]

Next ==
    LET predecessor[i] == IF i = 0 THEN counters[N-1] ELSE counters[i-1]
        successor[i]   == IF i = N-1 THEN counters[0] ELSE counters[i+1]
    IN
    \E i \in 0..N-1 :
        /\ (i = 0 /\ counters[i] = predecessor[i]) \/ (counters[i] # predecessor[i])
        /\ \/ (i = 0 /\ counters' = [counters EXCEPT ![i] = (counters[i] + 1) % M])
           \/ counters' = [counters EXCEPT ![i] = predecessor[i]]

Spec ==
    /\ Init
    /\ [][Next]_<<counters>>
    /\ WF_next(<<counters>>)

Stabilized ==
    \E i \in 0..N-1 :
        /\ counters[i] # predecessor(i)
        /\ \A j \in 0..i-1 : counters[j] = counters[0]
        /\ \A j \in i+1..N-1 : counters[j] = predecessor(j)

THEOREM Spec => <>[](Stabilized)

================================================================================