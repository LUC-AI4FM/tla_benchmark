------------------------------- MODULE BarrierSync -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES arrived

Init == arrived = {}

Next ==
    \/ \E p \in (1..N) \ arrival: arrived' = arrived \cup {p}
    \/ \E p \in arrived: /\ #arrived = N
                           /\ arrived' = {}

Spec ==
    /\ Init
    /\ [][Next]_<<arrived>>
    /\ WF_next(<<arrived>>)

TypeInvariant == \A p \in 1..N: p \in arrived \/ p \notin arrived

BarrierProperty ==
    [](arrival \/ (\A p \in (1..N) \ arrival: p \notin arrived))

arrival(p) == p \in arrived

SpecWithProperties ==
    /\ Spec
    /\ TypeInvariant
    /\ BarrierProperty

=============================================================================