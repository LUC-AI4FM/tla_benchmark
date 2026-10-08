---------------------------- MODULE ShortestPathTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

VARIABLES parent, dist, Edges

Infinity == Cardinality(Nodes) + 1

Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

IsConnected(E) ==
    LET ReachableFrom[S \in SUBSET Nodes] ==
        LET NewNodes == S \cup {m \in Nodes : \E n \in S : {n, m} \in E}
        IN IF NewNodes = S THEN S ELSE ReachableFrom[NewNodes]
    IN ReachableFrom[{Root}] = Nodes

ValidEdges == {E \in SUBSET {e \in SUBSET Nodes : Cardinality(e) = 2} : IsConnected(E)}

TypeOK ==
    /\ parent \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat \cup {Infinity}]
    /\ Edges \in ValidEdges
    /\ \A n \in Nodes : parent[n] = n \/ parent[n] \in Neighbors(n)

Init ==
    /\ Edges \in ValidEdges
    /\ parent = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

CanAdopt(n, m) ==
    /\ n /= Root
    /\ m \in Neighbors(n)
    /\ dist[m] /= Infinity
    /\ dist[m] < dist[n] \/ (dist[n] /= Infinity /\ dist[m] + 1 < dist[n])

Adopt(n, m) ==
    /\ CanAdopt(n, m)
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ UNCHANGED Edges

Update(n) ==
    \E m \in Neighbors(n) : Adopt(n, m)

Next ==
    \/ \E n \in Nodes : Update(n)
    \/ UNCHANGED <<parent, dist, Edges>>

vars == <<parent, dist, Edges>>

Fairness == \A n \in Nodes : WF_vars(Update(n))

Spec == Init /\ [][Next]_vars /\ Fairness

ParentInvariant ==
    \A n \in Nodes : parent[n] = n \/ parent[n] \in Neighbors(n)

DistanceInvariant ==
    \A n \in Nodes : dist[n] \in Nat \cup {Infinity}

RootInvariant ==
    /\ dist[Root] = 0
    /\ parent[Root] = Root

FiniteDistanceInvariant ==
    \A n \in Nodes :
        (dist[n] /= Infinity /\ dist[n] > 0) =>
            (parent[n] \in Neighbors(n) /\ dist[n] = dist[parent[n]] + 1)

Safety ==
    /\ TypeOK
    /\ ParentInvariant
    /\ DistanceInvariant
    /\ RootInvariant
    /\ FiniteDistanceInvariant

Stable ==
    \A n \in Nodes :
        \/ n = Root
        \/ (dist[n] = Infinity /\ parent[n] = n /\ \A m \in Neighbors(n) : dist[m] = Infinity)
        \/ (dist[n] /= Infinity /\ parent[n] \in Neighbors(n) /\ dist[n] = dist[parent[n]] + 1)

Liveness == <>Stable

=============================================================================