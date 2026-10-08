------------------------------- MODULE SpanningTree -------------------------------

CONSTANTS Nodes, Edges, Root, UpperBound

ASSUME Nodes \subseteq 1..UpperBound
ASSUME Root \in Nodes
ASSUME \A e \in Edges : Cardinality(e) = 2 /\ (\E n \in e: n \in Nodes)

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

Spec == Init /\ [][Next]_<<dist, parent>>

TypeOK ==
    /\ dist \in [Nodes -> 0..UpperBound]
    /\ parent \in [Nodes -> Nodes]

Safety ==
    /\ dist[Root] = 0
    /\ parent[Root] = Root
    /\ \A n \notin {n \in Nodes : Root \in Reachable(n)} :
        /\ dist[n] = UpperBound
        /\ parent[n] = n
        /\ \A m \in Neighbors(n) : dist[m] >= dist[n]
    /\ \A n \in Nodes \ {Root} :
        /\ dist[n] = dist[parent[n]] + 1
        /\ {n, parent[n]} \in Edges

Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

Reachable(n) ==
    LET rec(NodesLeft, Visited) ==
        IF NodesLeft = {} THEN Visited
        ELSE LET newVisited == Visited \cup (NodesLeft \cap {m \in Nodes : parent[m] \in Visited})
             IN  rec(NodesLeft \ newVisited, newVisited)
    IN  rec({n}, {})

Liveness ==
    <>[](dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE UpperBound] \/ \A u \in Nodes, v \in Neighbors(u) : dist[u] <= dist[v] + 1)

=============================================================================