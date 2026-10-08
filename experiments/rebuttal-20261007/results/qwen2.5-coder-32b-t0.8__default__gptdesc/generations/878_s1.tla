---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxCardinality
ASSUME Root \in Nodes /\ Cardinality(Nodes) <= MaxCardinality

VARIABLES mom, dist

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
    \/ /\ \E u, v \in Nodes : u # v
       /\ dist[u] > dist[v]
       /\ LET newDist == CHOOSE d \in (1..dist[u]-1) : TRUE
          IN /\ mom' = [mom EXCEPT ![u] = v]
             /\ dist' = [dist EXCEPT ![u] = newDist]

Safety ==
    \/ \A u, v \in Nodes : u # Root => \E p \in Nodes : \A x \in (p..u) : mom[x] = p
    \/ \A u \in Nodes : dist[u] <= dist[Root]

Termination ==
    \A u \in Nodes : dist[u] < MaxCardinality

Liveness == <>[] Termination /\ []<> (\E u \in Nodes : dist[u] >= MaxCardinality)

Spec == Init /\ [][Next]_<< >> /\ WF_next(Next) /\ Safety /\ Liveness

=============================================================================