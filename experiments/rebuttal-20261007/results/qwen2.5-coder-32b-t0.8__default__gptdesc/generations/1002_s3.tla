------------------------------- MODULE BarrierSync -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES pc

Init == /\ pc \in [1..N -> {"b0"}]

Next ==
    \/ /\ E \in SUBSET (1..N) /\ Cardinality(E) < N
       /\ \A p \in E: pc[p] = "b0" -> pc' = [pc EXCEPT ![p] = "b1"]
    \/ /\ Cardinality({p \in 1..N : pc[p] = "b1"}) = N
       -> pc' = [pc \in (1..N) -> "b0"]

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

TypeOK == pc \in [1..N -> {"b0", "b1"}]

InvTemporalBarrier ==
    /\ [](\A p \in 1..N: [](pc[p] = "b1" => <>[](\A q \in 1..N: pc[q] = "b1")))

SpecWithProperties ==
    /\ Spec
    /\ TypeOK
    /\ InvTemporalBarrier

=============================================================================