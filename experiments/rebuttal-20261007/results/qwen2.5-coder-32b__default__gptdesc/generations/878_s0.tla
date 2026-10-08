------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality
VARIABLES mom, dist

Init == /\ mom \in [Nodes -> Nodes]
        /\ dist \in [Nodes -> NatUnion({MaxCardinality})]
        /\ (\A n \in Nodes \ {Root} : mom[n] = n)
        /\ (\A n \in Nodes \ {Root} : dist[n] = MaxCardinality)
        /\ mom[Root] = Root
        /\ dist[Root] = 0

Next == \/ CHOOSE u \in Nodes, v \in Nodes :
                /\ dist[u] > dist[v]
                /\ dist[v] < MaxCardinality
                /\ <<u, v>> \in Edges \/ <<v, u>> \in Edges
                /\ LET newDist \in 1..dist[u]-1
                   IN /\ mom' = [mom EXCEPT ![u] = v]
                      /\ dist' = [dist EXCEPT ![u] = newDist]

Spec == Init /\ [][Next]_<<mom, dist>> \/ WF_next(Next)

Edges == SUBSET (Nodes \X Nodes) \ { <<n, n>> \in Nodes }

Termination ==
    /\ (\A u \in Nodes : mom[u] \in Nodes)
    /\ (\A u \in Nodes : dist[u] < MaxCardinality)
    /\ (\A u \in Nodes \ {Root} : dist[u] = 1 + dist[mom[u]])
    /\ (\A u \in Nodes \ {Root} : mom[u] # u)

Safety == [](Termination -> Termination)

Liveness == <>(\A n \in Nodes : mom[n] = Root)

WF_next(Next) == WF_<<mom, dist>>(Next)

=============================================================================