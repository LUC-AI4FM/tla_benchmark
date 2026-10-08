------------------------------- MODULE BarrierSync -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES pc

Init == /\ pc \in [1..N -> {"b0"}]

Next ==
    \/ \E i \in 1..N : /\ pc[i] = "b0"
                           /\ pc' = [pc EXCEPT ![i] = "b1"]
    \/ /\ A i \in 1..N : pc[i] = "b1"
       /\ pc' \in [1..N -> {"b0"}]

TypeOk == pc \in [1..N -> {"b0", "b1"}]

TemporalBarrier ==
    [](\/ \A i \in 1..N : pc[i] # "b1"
        \/ \E i \in 1..N : /\ pc[i] = "b1"
                           /\ \A j \in 1..N : pc[j] = "b1")

Spec == Init /\ [][Next]_<<pc>> /\ TypeOk /\ TemporalBarrier

=============================================================================