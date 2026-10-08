------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, UpperBound
ASSUME Root \in Nodes
ASSUME \A e \in Edges : Cardinality(e) = 2 /\ (\E n \in Nodes : e = {n})
ASSUME UpperBound \in Nat

VARIABLES dist, parent

Init == 
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE UpperBound]
    /\ parent = [n \in Nodes |-> n]

Next ==
    \E u \in Nodes, v \in Nodes :
        /\ {u, v} \in Edges
        /\ dist[u] > dist[v] + 1
        /\ \E newDist \in (dist[v]+1) .. (dist[u]-1) :
            /\ dist' = [dist EXCEPT ![u] = newDist]
            /\ parent' = [parent EXCEPT ![u] = v]

Spec ==
    Init /\ [][Next]_<<dist, parent>>

Termination ==
    [](dist[u] <= dist[v] + 1 \/ \A w \in Nodes : {u, w} \notin Edges)
        /\ (dist[Root] = 0 /\ parent[Root] = Root)

ValidSpanningTree ==
    /\ dist[Root] = 0
    /\ parent[Root] = Root
    /\ \A n \in Nodes :
        \/ (n = Root)
        \/ (\E p \in Nodes : parent[n] = p /\ {n, p} \in Edges /\ dist[n] = dist[p] + 1)
        \/ (\A m \in Nodes : {n, m} \notin Edges => dist[n] = UpperBound /\ parent[n] = n)

Safety ==
    ValidSpanningTree

Liveness ==
    <>(Termination)

THEOREM Spec => []Safety
THEOREM Spec => <>Liveness

=============================================================================