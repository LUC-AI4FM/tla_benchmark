---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME MaxCardinality \in Nat
ASSUME MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

vars == <<mom, dist>>

Neighbors(n) == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}

TypeInvariant ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Update(n, m, d) ==
    /\ m \in Neighbors(n)
    /\ dist[m] < dist[n]
    /\ d > dist[m]
    /\ d < dist[n]
    /\ mom' = [mom EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = d]

Next ==
    \E n \in Nodes : \E m \in Nodes : \E d \in 0..MaxCardinality :
        Update(n, m, d)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated == ~ENABLED Next

ReachableFromRoot ==
    LET RECURSIVE Reachable(_)
        Reachable(S) ==
            LET NewNodes == {n \in Nodes : \E m \in S : m \in Neighbors(n)}
            IN IF NewNodes \subseteq S
               THEN S
               ELSE Reachable(S \cup NewNodes)
    IN Reachable({Root})

IsTree ==
    /\ mom[Root] = Root
    /\ \A n \in Nodes \ {Root} : 
        /\ mom[n] \in Neighbors(n)
        /\ dist[n] = dist[mom[n]] + 1

PostCondition ==
    /\ IsTree
    /\ \A n \in ReachableFromRoot : dist[n] < MaxCardinality

Safety == Terminated => PostCondition

Liveness == <>Terminated

AllNodesHaveRootAsAncestor ==
    \A n \in Nodes : <>(mom[n] = Root)

=============================================================================