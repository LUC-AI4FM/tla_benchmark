------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME \A e \in Edges : e \in SUBSET Nodes /\ Cardinality(e) = 2
ASSUME MaxCardinality \in Nat /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

Init == 
    /\ dist[Root] = 0
    /\ \A n \in Nodes \ {Root} : dist[n] = MaxCardinality
    /\ \A n \in Nodes : mom[n] = n

Next ==
    \E n \in Nodes, m \in Nodes :
        /\ {n, m} \in Edges
        /\ dist[m] + 1 < dist[n]
        /\ \E d \in (dist[m]+1) ..< dist[n] :
            /\ dist' = [dist EXCEPT ![n] = d]
            /\ mom' = [mom EXCEPT ![n] = m]

Spec ==
    Init /\ [][Next]_<<mom, dist>> /\ WF_next(<<mom, dist>>)

TypeOK ==
    /\ \A n \in Nodes : dist[n] \in 0..MaxCardinality
    /\ \A n \in Nodes : mom[n] \in Nodes

Safety ==
    ~(\E n \in Nodes, m \in Nodes :
        {n, m} \in Edges
        /\ dist[m] + 1 < dist[n])
    -> 
    (\A n \in Nodes :
        \/ /\ n = Root
           /\ dist[n] = 0
           /\ mom[n] = Root
        \/ /\ dist[n] = MaxCardinality
           /\ mom[n] = n
           /\ \A m \in {m \in Nodes : {n, m} \in Edges} : dist[m] = MaxCardinality
        \/ /\ dist[n] = dist[mom[n]] + 1
           /\ {n, mom[n]} \in Edges)

Liveness ==
    <>(\A n \in Nodes :
        \/ /\ n = Root
           /\ dist[n] = 0
           /\ mom[n] = Root
        \/ /\ dist[n] = MaxCardinality
           /\ mom[n] = n
           /\ \A m \in {m \in Nodes : {n, m} \in Edges} : dist[m] = MaxCardinality
        \/ /\ dist[n] = dist[mom[n]] + 1
           /\ {n, mom[n]} \in Edges)

=============================================================================