------------------------------- MODULE SpanningTree -------------------------------

CONSTANTS Nodes, Root, MaxCardinality

VARIABLES mom, dist

ASSUME Root \in Nodes
ASSUME MaxCardinality > 0

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
    \E u \in Nodes, v \in Nodes :
        /\ u # v
        /\ dist[v] < dist[u]
        /\ mom' = [mom EXCEPT ![u] = v]
        /\ dist' = [dist EXCEPT ![u] = SOME d \in 1..(dist[u]-1)]

Spec ==
    /\ Init
    /\ WF_<<Next>>_<<Node>>
    /\ []\[<<Node>> \|-> Next]

Safety ==
    [](dist[Root] = 0)
    /\ <>(\A n \in Nodes : mom[n] \in Nodes)
    /\ <>(\A n \in Nodes : dist[n] >= 0)
    /\ <>(\A n \in Nodes : n = Root \/ dist[mom[n]] < dist[n])
    /\ <>(\A n \in Nodes : Distinct({mom[k] : k \in {n} \cup {mom[k] : k \in {n}}}))
    /\ <>(\A n \in Nodes : n = Root \/ mom[n] # n)
    /\ <>(\A n \in Nodes : dist[n] <= MaxCardinality)

Liveness ==
    <>(\A n \in Nodes : mom[n] = Root)

TypeOK == TRUE

Node == CHOOSE u \in Nodes : TRUE

=============================================================================