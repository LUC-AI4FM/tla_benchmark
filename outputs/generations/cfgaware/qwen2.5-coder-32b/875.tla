------------------------------- MODULE SpanningTree -------------------------------

CONSTANTS Nodes, Root

VARIABLES mom, dist

ASSUME Root \in Nodes
ASSUME Cardinality(Nodes) > 1

(*--algorithm spanning-tree
variables 
    mom = [n \in Nodes |-> n],
    dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE \infinity];

define Edges == [n \in Nodes |-> {m \in Nodes \ {n} : TLC!RandomElement({TRUE, FALSE})}]
    
Next ==
    \E u \in Nodes :
        LET neighbors == Edges[u]
            minDistNode == CHOOSE v \in neighbors : dist[v] < dist[u]
        IN
        /\ minDistNode \in neighbors
        /\ mom' = [mom EXCEPT ![u] = minDistNode]
        /\ dist' = [dist EXCEPT ![u] = dist[minDistNode]]

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat \cup {\infinity}]
    /\ \A u \in Nodes : mom[u] \in Nodes
    /\ \A u \in Nodes : (dist[u] = 0) => (u = Root)

IsSpanningTree ==
    LET tree == {<<mom[n], n>> : n \in Nodes \ {Root}}
        nodesInTree == {n \in Nodes : \E m \in Nodes : <<m, n>> \in tree}
    IN
        /\ Cardinality(nodesInTree) = Cardinality(Nodes)
        /\ \A u \in Nodes \ {Root} : u \in nodesInTree
        /\ WF_vars(tree)

Safety ==
    [](TypeOK => <>[](IsSpanningTree))

Liveness ==
    <>(TypeOK => IsSpanningTree)

Spec ==
    TypeOK /\ WF_vars(Next) /\ []<>(Next) /\ Safety /\ Liveness

end algorithm *)
=============================================================================