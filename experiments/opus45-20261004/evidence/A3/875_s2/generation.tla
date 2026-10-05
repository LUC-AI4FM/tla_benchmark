---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

vars == <<mom, dist>>

\* Generate random edges: for each node, pick a random subset of other nodes
\* This creates an undirected graph
EdgesFrom(n) == RandomElement(SUBSET (Nodes \ {n}))

\* We use a function to store the random edges, generated once
VARIABLE mom, dist, edges

allvars == <<mom, dist, edges>>

\* For the undirected graph, an edge exists if either direction was chosen
Edge(m, n) == n \in edges[m] \/ m \in edges[n]

Neighbors(n) == {m \in Nodes : Edge(m, n)}

TypeOK == 
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat \cup {-1}]
    /\ edges \in [Nodes -> SUBSET Nodes]

\* Initialization: every node points to itself, only root has distance 0
\* Other nodes have distance -1 (representing infinity/unreachable initially)
Init == 
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE -1]
    /\ edges = [n \in Nodes |-> RandomElement(SUBSET (Nodes \ {n}))]

\* A node can adopt a neighbor with strictly smaller distance
\* and choose an intermediate smaller distance value
\* We use -1 to represent infinity (unreachable)
\* A distance d1 is "smaller" than d2 if d1 >= 0 and (d2 = -1 or d1 < d2)
Smaller(d1, d2) == 
    /\ d1 >= 0
    /\ \/ d2 = -1
       \/ d1 < d2

\* Node n adopts neighbor m with smaller distance and picks intermediate distance
Adopt(n, m) ==
    /\ n # Root
    /\ Edge(n, m)
    /\ Smaller(dist[m], dist[n])
    /\ \E d \in (dist[m] + 1)..(IF dist[n] = -1 THEN dist[m] + 1 ELSE dist[n] - 1) \cup {dist[m] + 1}:
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]
    /\ UNCHANGED edges

Next == \E n \in Nodes : \E m \in Nodes : Adopt(n, m)

\* Postcondition: characterizes a rooted spanning tree or unreachable nodes
\* A node is either:
\* - the root (points to itself, distance 0)
\* - reachable (points to a neighbor with distance one less)
\* - unreachable (points to itself, distance -1, no reachable neighbors)
Reachable(n) == dist[n] >= 0

PostCondition ==
    \A n \in Nodes :
        \/ /\ n = Root
           /\ mom[n] = Root
           /\ dist[n] = 0
        \/ /\ n # Root
           /\ Reachable(n)
           /\ Edge(n, mom[n])
           /\ dist[mom[n]] = dist[n] - 1
           /\ dist[n] > 0
        \/ /\ n # Root
           /\ ~Reachable(n)
           /\ dist[n] = -1
           /\ mom[n] = n
           /\ \A m \in Neighbors(n) : ~Reachable(m)

\* Quiescence: no node can make progress
Quiescent == ~ENABLED Next

\* Safety: quiescence implies postcondition
SafetyProperty == Quiescent => PostCondition

\* Liveness: eventually the postcondition holds
LivenessProperty == <>PostCondition

\* Specification with weak fairness
Spec == Init /\ [][Next]_allvars /\ WF_allvars(Next)

\* Invariants and properties to check
Invariants == TypeOK /\ SafetyProperty

=============================================================================