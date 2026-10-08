------------------------------- MODULE SpanningTree -------------------------------

CONSTANTS Nodes, Edges, Root, Bound

ASSUME 
    \A n \in Nodes : n \notin {}
    \A e \in Edges : /\ Cardinality(e) = 2
                     /\ e[1] \in Nodes
                     /\ e[2] \in Nodes
                     /\ e[1] # e[2]
                     /\ {e[1], e[2]} \notin SUBSET Edges EXCEPT {e}
    Root \in Nodes
    Bound \geq Cardinality(Nodes)

VARIABLES dist, parent

Init == 
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Bound]
    /\ parent = [n \in Nodes |-> IF n = Root THEN Root ELSE n]

Next ==
    \E n \in Nodes :
        LET neighbors == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}
            minDist == Min({dist[m] : m \in neighbors})
        IN
        /\ dist[n] > minDist + 1
        /\ dist' = [dist EXCEPT ![n] = minDist + 1]
        /\ parent' = [parent EXCEPT ![n] = CHOOSE m \in neighbors : dist[m] = minDist]
        /\ UNCHANGED <<Nodes, Edges, Root, Bound>>

Spec ==
    Init /\ [][Next]_<<dist, parent>>

TypeOK ==
    /\ dist \in [Nodes -> 0..Bound]
    /\ parent \in [Nodes -> Nodes]

Safety ==
    LET reachable == {n \in Nodes : dist[n] < Bound}
        treeEdges == {(parent[n], n) : n \in reachable EXCEPT Root}
    IN
        /\ \A n \in reachable : dist[n] = (CHOOSE p \in reachable : parent[p] = n) + 1
        /\ \A e \in treeEdges : e[1] # e[2]
        /\ \A n \in Nodes : n = Root \/ n \notin reachable \/ <<parent[n], n>> \in treeEdges

Liveness ==
    [](TypeOK /\ Safety) => <>(\A n \in Nodes : dist'[n] = dist[n] /\ parent'[n] = parent[n])

=============================================================================