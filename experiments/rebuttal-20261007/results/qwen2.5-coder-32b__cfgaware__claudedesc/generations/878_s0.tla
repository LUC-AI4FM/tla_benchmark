------------------------------- MODULE SpanningTree -------------------------------

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME \A e \in Edges : e \in SUBSET Nodes /\ Cardinality(e) = 2
ASSUME MaxCardinality \in Nat /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

Init == 
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
    /\ mom = [n \in Nodes |-> n]

Next ==
    \E n \in Nodes, m \in Nodes :
        /\ {n, m} \in Edges
        /\ dist[m] + 1 < dist[n]
        /\ \E d \in (dist[m]+1) ..< dist[n] : 
            /\ dist' = [dist EXCEPT ![n] = d]
            /\ mom' = [mom EXCEPT ![n] = m]

Spec ==
    Init /\ [][Next]_<<mom, dist>> /\ WF_next(Next)

TypeOK ==
    /\ dist \in [Nodes -> 0..MaxCardinality]
    /\ mom \in [Nodes -> Nodes]

Safety ==
    ~(\E n \in Nodes : {n, mom[n]} \notin Edges \/ dist[n] <> dist[mom[n]] + 1)
        \/ (dist[Root] = 0 /\ mom[Root] = Root
            /\ \A n \in Nodes \ {Root} :
                (dist[n] = MaxCardinality <=> (\A m \in Nodes : {n, m} \notin Edges))
                /\ (dist[n] # MaxCardinality => dist[n] = dist[mom[n]] + 1 /\ {n, mom[n]} \in Edges))

Liveness ==
    <>(\A n \in Nodes :
        (dist[n] = MaxCardinality <=> (\A m \in Nodes : {n, m} \notin Edges))
        /\ (dist[n] # MaxCardinality => dist[n] = dist[mom[n]] + 1 /\ {n, mom[n]} \in Edges))

WF_next(action) ==
    \/ ~(\E n \in Nodes, m \in Nodes : {n, m} \in Edges /\ dist[m] + 1 < dist[n])
    \/ <>(\E n \in Nodes, m \in Nodes :
            {n, m} \in Edges
            /\ dist[m] + 1 < dist[n]
            /\ \E d \in (dist[m]+1) ..< dist[n] : 
                action = [mom' |-> [mom EXCEPT ![n] = m],
                          dist' |-> [dist EXCEPT ![n] = d]])

=============================================================================