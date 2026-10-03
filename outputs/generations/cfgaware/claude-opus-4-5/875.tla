---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

vars == <<mom, dist>>

-----------------------------------------------------------------------------

\* Generate random edges: for each node, pick a random subset of other nodes
\* This creates an undirected graph represented as a set of edges
Edges ==
    LET 
        \* For each node, generate random neighbors
        RandomNeighbors(n) == RandomElement(SUBSET (Nodes \ {n}))
        \* Create edge pairs from node to its random neighbors
        EdgesFromNode(n) == {{n, m} : m \in RandomNeighbors(n)}
    IN
        UNION {EdgesFromNode(n) : n \in Nodes}

\* Neighbors of a node in the graph
Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

\* Maximum possible distance (used for unreachable nodes)
MaxDist == Cardinality(Nodes)

-----------------------------------------------------------------------------

\* Initial state: every node points to itself, only root has distance 0
Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]

\* A node n can adopt a neighbor m with strictly smaller distance
\* and choose an intermediate distance value
Adopt(n, m) ==
    /\ n \in Nodes
    /\ m \in Neighbors(n)
    /\ dist[m] < dist[n]
    /\ \E d \in (dist[m]+1)..dist[n] :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

\* Next action: some node adopts a neighbor with smaller distance
Next ==
    \E n \in Nodes : \E m \in Neighbors(n) : Adopt(n, m)

-----------------------------------------------------------------------------

\* Type correctness invariant
TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxDist]

\* Postcondition: characterizes a rooted spanning tree or unreachable nodes
\* For each node: either it's the root, or it points to a neighbor with distance one less,
\* or it's unreachable (distance MaxDist and points to itself)
Postcondition ==
    \A n \in Nodes :
        \/ (n = Root /\ mom[n] = Root /\ dist[n] = 0)
        \/ (n # Root /\ mom[n] \in Neighbors(n) /\ dist[n] = dist[mom[n]] + 1)
        \/ (dist[n] = MaxDist /\ mom[n] = n)

\* System is quiescent when no more moves are possible
Quiescent ==
    ~(\E n \in Nodes : \E m \in Neighbors(n) : dist[m] < dist[n])

\* Safety: quiescence implies the postcondition
Safety ==
    Quiescent => Postcondition

\* Liveness: eventually the postcondition holds
Liveness ==
    <>Postcondition

\* Specification with weak fairness on Next
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================