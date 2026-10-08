------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Edges, Root, Bound
ASSUME Root \in Nodes
ASSUME \A n \in Nodes : \A m \in Nodes : (n = m) \/ <<n, m>> \in Edges => <<m, n>> \in Edges
ASSUME Bound >= Cardinality(Nodes)

VARIABLES dist, parent

Init == /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Bound]
        /\ parent = [n \in Nodes |-> n]

Next ==
    LET neighbors(n) == {m \in Nodes : <<n, m>> \in Edges}
        update(n, newDist) == /\ dist' = [dist EXCEPT ![n] = newDist]
                                /\ parent' = [parent EXCEPT ![n] = CHOOSE p \in neighbors(n) : dist[p] < newDist]
    IN \/ \E n \in Nodes \ {Root} :
            LET minNeighborDist == Min({dist[m] : m \in neighbors(n)})
            IN /\ minNeighborDist + 1 < dist[n]
               /\ update(n, minNeighborDist + 1)
       \/ UNCHANGED <<dist, parent>>

Spec ==
    /\ Init
    /\ [][Next]_<<dist, parent>>
    /\ WF_next(<<dist, parent>>)

Quiescence ==
    \A n \in Nodes :
        LET neighborsDist == {dist[m] : m \in {m \in Nodes : <<n, m>> \in Edges}}
        IN dist[n] <= Min(neighborsDist) + 1

Safety ==
    /\ Quiescence
    /\ \A n \in Nodes :
            \/ n = Root
            \/ /\ parent[n] \in neighbors(n)
               /\ dist[n] = dist[parent[n]] + 1
    /\ \A n \in Nodes :
            \/ dist[n] < Bound
            \/ parent[n] = n

Liveness ==
    <>[]Quiescence

THEOREM Spec => []Safety /\ Liveness
=============================================================================