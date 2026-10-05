---------------------------- MODULE spanning_tree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

vars == <<mom, dist>>

\* Generate random edges: for each node, pick a random subset of other nodes
\* This creates an undirected graph represented as a set of edges
EdgesFrom(n) == RandomElement(SUBSET (Nodes \ {n}))

\* We need to generate edges consistently, so we define it as a function
\* that maps each node to its neighbors
RECURSIVE GenerateNeighbors(_)
GenerateNeighbors(S) == 
    IF S = {} THEN [n \in {} |-> {}]
    ELSE LET n == CHOOSE x \in S : TRUE
             rest == GenerateNeighbors(S \ {n})
         IN [x \in S |-> IF x = n THEN EdgesFrom(n) ELSE rest[x]]

Neighbors == GenerateNeighbors(Nodes)

\* Two nodes are connected if there's an edge between them (undirected)
IsNeighbor(n1, n2) == n2 \in Neighbors[n1] \/ n1 \in Neighbors[n2]

\* The set of neighbors for a given node
NeighborSet(n) == {m \in Nodes : IsNeighbor(n, m)}

\* Maximum possible distance (used for unreachable nodes)
MaxDist == Cardinality(Nodes)

\* Type correctness invariant
TypeOK == 
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat]
    /\ \A n \in Nodes : dist[n] <= MaxDist

\* Initial state: every node points to itself, root has distance 0, others have MaxDist
Init == 
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]

\* A node n can adopt a neighbor m with strictly smaller distance
\* and choose an intermediate distance value
Adopt(n, m) ==
    /\ n # Root
    /\ IsNeighbor(n, m)
    /\ dist[m] < dist[n]
    /\ \E d \in (dist[m]+1)..dist[n] :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

\* Next action: some node adopts a neighbor with smaller distance
Next == \E n \in Nodes : \E m \in Nodes : Adopt(n, m)

\* Postcondition: characterizes a rooted spanning tree or unreachable nodes
\* For reachable nodes: they form a tree rooted at Root
\* For unreachable nodes: they still point to themselves with MaxDist
PostCondition ==
    /\ mom[Root] = Root
    /\ dist[Root] = 0
    /\ \A n \in Nodes \ {Root} :
        \/ /\ dist[n] < MaxDist                          \* Node is reachable
           /\ IsNeighbor(n, mom[n])                      \* Parent is a neighbor
           /\ dist[n] = dist[mom[n]] + 1                 \* Distance is parent's distance + 1
        \/ /\ dist[n] = MaxDist                          \* Node is unreachable
           /\ mom[n] = n                                 \* Points to itself

\* System is quiescent when no more moves are possible
Quiescent == ~ENABLED Next

\* Safety: quiescence implies postcondition
Safety == Quiescent => PostCondition

\* Liveness: eventually the postcondition holds
Liveness == <>PostCondition

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================