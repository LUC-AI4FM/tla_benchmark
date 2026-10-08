------------------------------- MODULE TokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K
ASSUME N > 0 /\ K > N

VARIABLES counters

Init == /\ counters \in [0 ..< N -> 0..K-1]
        /\ (\E i \in 0 ..< N : counters[i] = 0)

Next ==
    LET predecessor[i \in 0 ..< N] == IF i = 0 THEN N - 1 ELSE i - 1
        newCounters == [i \in 0 ..< N |-> 
                            IF counters[i] # counters[predecessor[i]] 
                            THEN (IF i = 0 THEN (counters[i] + 1) % K ELSE counters[predecessor[i]])
                            ELSE counters[i]]
    IN /\ counters' = newCounters

Spec == Init /\ [][Next]_<<counters>>

TokenExists ==
    \A s \in StateSpace : (\E i \in 0 ..< N : s.counters[i] # s.counters[IF i = 0 THEN N - 1 ELSE i - 1])

SingleToken ==
    \A s \in StateSpace : (Cardinality({i \in 0 ..< N : s.counters[i] # s.counters[IF i = 0 THEN N - 1 ELSE i - 1]}) = 1)

StableSingleToken ==
    []( /\ TokenExists
         /\ SingleToken )

Liveness ==
    <>(\A i \in 0 ..< N : counters'[i] # counters[i]) /\ StableSingleToken

Fairness == WF_next(<<counters>>)

THEOREM Spec => []TokenExists
THEOREM Spec => Liveness
=============================================================================