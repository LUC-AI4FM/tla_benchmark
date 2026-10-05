---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

\* Generate random edges: for each node, pick a random subset of other nodes
\* This creates an undirected graph
RandomSubset(S) == RandomElement(SUBSET S)

EdgesFrom == [n \in Nodes |-> RandomSubset(Nodes \ {n})]

\* Edges as a symmetric relation (undirected graph)
Edges == {<<u, v>> \in Nodes \X Nodes : v \in EdgesFrom[u] \/ u \in EdgesFrom[v]}

\* Neighbors of a node
Neighbors(n) == {m \in Nodes : <<n, m>> \in Edges}

VARIABLES mom, dist

vars == <<mom, dist>>

\* Maximum possible distance (used for unreachable nodes)
MaxDist == Cardinality(Nodes)

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxDist]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]

\* A node can adopt a neighbor with strictly smaller distance
\* and choose an intermediate distance value
Adopt(n) ==
    /\ n # Root
    /\ \E neighbor \in Neighbors(n) :
        /\ dist[neighbor] < dist[n] - 1 \/ (dist[neighbor] < dist[n] /\ dist[neighbor] < MaxDist)
        /\ dist[neighbor] + 1 < dist[n]
        /\ \E newDist \in (dist[neighbor] + 1)..(dist[n] - 1) :
            /\ mom' = [mom EXCEPT ![n] = neighbor]
            /\ dist' = [dist EXCEPT ![n] = newDist]

\* Alternative: direct adoption when neighbor's distance is exactly one less
DirectAdopt(n) ==
    /\ n # Root
    /\ \E neighbor \in Neighbors(n) :
        /\ dist[neighbor] + 1 < dist[n]
        /\ mom' = [mom EXCEPT ![n] = neighbor]
        /\ dist' = [dist EXCEPT ![n] = dist[neighbor] + 1]

Next == \E n \in Nodes : DirectAdopt(n)

\* Postcondition: characterizes a rooted spanning tree or unreachable nodes
\* A node is either:
\* 1. The root (points to itself, distance 0)
\* 2. Reachable: points to a neighbor with distance one less
\* 3. Unreachable: distance is MaxDist and points to itself

IsReachable(n) == dist[n] < MaxDist

PostCondition ==
    \A n \in Nodes :
        \/ (n = Root /\ mom[n] = Root /\ dist[n] = 0)
        \/ (n # Root /\ IsReachable(n) /\ 
            mom[n] \in Neighbors(n) /\ 
            dist[n] = dist[mom[n]] + 1)
        \/ (n # Root /\ ~IsReachable(n) /\ 
            dist[n] = MaxDist /\ 
            mom[n] = n)

\* Quiescence: no more actions are enabled
Quiescent ==
    ~(\E n \in Nodes : 
        /\ n # Root
        /\ \E neighbor \in Neighbors(n) :
            dist[neighbor] + 1 < dist[n])

\* Safety: quiescence implies postcondition
SafetyProperty == Quiescent => PostCondition

\* Liveness: eventually the postcondition holds
LivenessProperty == <>PostCondition

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Invariants to check
Invariants == TypeOK /\ SafetyProperty

=============================================================================