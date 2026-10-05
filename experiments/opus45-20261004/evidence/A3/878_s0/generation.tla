---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, Naturals

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME Edges \subseteq (Nodes \times Nodes)
ASSUME \A e \in Edges : e[1] # e[2]
ASSUME \A e \in Edges : <<e[2], e[1]>> \in Edges
ASSUME MaxCardinality \in Nat
ASSUME MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

vars == <<mom, dist>>

Neighbors(n) == {m \in Nodes : <<n, m>> \in Edges}

TypeInvariant ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Update(n, m) ==
    /\ m \in Neighbors(n)
    /\ dist[m] < dist[n]
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

Next ==
    \E n \in Nodes : \E m \in Nodes : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated ==
    ~(\E n \in Nodes : \E m \in Neighbors(n) : dist[m] < dist[n] - 1)

Reachable == 
    LET RECURSIVE ReachableFrom(_)
        ReachableFrom(S) ==
            LET NewNodes == {m \in Nodes : \E n \in S : <<n, m>> \in Edges}
            IN IF NewNodes \subseteq S
               THEN S
               ELSE ReachableFrom(S \cup NewNodes)
    IN ReachableFrom({Root})

IsTree ==
    /\ mom[Root] = Root
    /\ \A n \in Nodes \ {Root} : 
        (n \in Reachable) => (mom[n] \in Neighbors(n) /\ dist[n] = dist[mom[n]] + 1)
    /\ \A n \in Nodes : 
        (n \notin Reachable) => (mom[n] = n /\ dist[n] = MaxCardinality)

PostCondition ==
    /\ IsTree
    /\ \A n \in Reachable : dist[n] < MaxCardinality

Safety == Terminated => PostCondition

Liveness == <>Terminated

RECURSIVE Ancestor(_, _)
Ancestor(n, k) ==
    IF k = 0 THEN n
    ELSE IF mom[n] = n THEN n
    ELSE Ancestor(mom[n], k - 1)

HasRootAsAncestor(n) ==
    \E k \in 0..Cardinality(Nodes) : Ancestor(n, k) = Root

EventuallyRootParent == \A n \in Reachable : <>(HasRootAsAncestor(n))

=============================================================================