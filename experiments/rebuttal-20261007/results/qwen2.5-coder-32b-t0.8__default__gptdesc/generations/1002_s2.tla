------------------------------ MODULE BarrierSync ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES pc \* Program counter for each process

Init == 
    /\ pc \in [1..N -> {"b0"}]

Next ==
    \/ /\ E \subseteq (1..N) /\ Cardinality(E) < N
       /\ \/ /\ \/ \E i \in E: pc'[i] = "b1" /\ \A j \notin E: pc'[j] = pc[j]
          \/ /\ \E i \in E: pc[i] = "b0" /\ pc'[i] = "b0"
             /\ \A j \notin E: pc'[j] = pc[j]
    \/ /\ Cardinality({i \in 1..N : pc[i] = "b1"}) = N
       /\ pc' = [1..N -> "b0"]

Spec ==
    Init /\ [][Next]_<<pc>>

TypeOK ==
    pc \in [1..N -> {"b0", "b1"}]

TemporalBarrierProperty ==
    [](\/ pc[i] = "b0" \/ (\A j \in 1..N: pc[j] = "b1"))

SafetySpec == TypeOK /\ TemporalBarrierProperty

LivenessSpec ==
    <>[](Cardinality({i \in 1..N : pc[i] = "b1"}) = N)

WF ==
    WF_next(pc, Next)

=============================================================================