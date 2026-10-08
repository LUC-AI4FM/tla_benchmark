------------------------------- MODULE BarrierSync -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES pc

Init == /\ pc \in [1..N -> {"b0"}]
        /\ Cardinality(DOMAIN pc) = N

Next ==
    \/ \E i \in 1..N : /\ pc[i] = "b0"
                         /\ pc' = [pc EXCEPT ![i] = "b1"]
    \/ /\ A\forall i \in 1..N : pc[i] = "b1"
       /\ pc' = [pc EXCEPT ! = "b0"]

Spec == Init /\ [][Next]_<<pc>>

TypeOK ==
    /\ pc \in [1..N -> {"b0", "b1"}]
    /\ Cardinality(DOMAIN pc) = N

TemporalBarrier ==
    [](\/ A\forall i \in 1..N : pc[i] = "b0"
        \/ (\E j \in 1..N : pc[j] = "b1") => A\forall i \in 1..N : pc[i] = "b1"))

Inv == TypeOK /\ TemporalBarrier

THEOREM Spec => []Inv
=============================================================================