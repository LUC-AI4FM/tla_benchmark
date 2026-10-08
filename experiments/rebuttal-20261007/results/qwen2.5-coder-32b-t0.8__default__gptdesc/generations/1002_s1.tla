------------------------------ MODULE BarrierSync ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES pc \* Program counter function: [1..N -> {"b0", "b1"}]

Init == /\ pc \in [1..N -> {"b0"}]
        /\ N > 0

Next == \/ \/ \E p \in 1..N : /\ pc[p] = "b0"
                                  /\ /\ pc' = [pc EXCEPT ![p] = "b1"]
                                  /\ \A q \in (1..N) \ {p} : pc'[q] = pc[q]
          \/ /\ pc = [1..N -> {"b1"}]
             /\ pc' = [1..N -> {"b0"}]

Spec == /\ Init
        /\ SF_<<Next>>
        /\ WF_<<Next>> (pc)

TypeOk == pc \in [1..N -> {"b0", "b1"}]

BarrierSafety == \/ pc = [1..N -> {"b0"}]
                   \/ \A p \in 1..N : pc[p] = "b1"

SpecTE == Spec /\ [][TypeOk]_<<Next>> /\ []BarrierSafety_<<Next>>

=============================================================================