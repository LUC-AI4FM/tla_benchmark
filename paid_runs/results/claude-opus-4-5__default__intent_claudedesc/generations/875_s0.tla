---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Nodes,          \* The set of all nodes in the graph
    Root,           \* The designated root node
    MaxDist         \* Upper bound for distance (should be >= Cardinality(Nodes))

VARIABLES
    edges,          \* The set of undirected edges (represented as sets of two nodes)
    dist,           \* dist[n] = current distance estimate for node n
    parent          \* parent[n] = current parent pointer for node n

vars == <<edges, dist, parent>>

\* Helper: Get neighbors of a node in the graph
Neighbors(n) == {m \in Nodes : {n, m} \in edges}

\* Generate a random graph topology
\* We use a set of all possible edges and let TLC explore different subsets
AllPossibleEdges == {{n, m} : n, m \in Nodes \ {n}}

\* Type invariant
TypeOK ==
    /\ edges \subseteq AllPossibleEdges
    /\ dist \in [Nodes -> 0..MaxDist]
    /\ parent \in [Nodes -> Nodes]

\* Initial state: random graph, root has distance 0, others have MaxDist
Init ==
    /\ edges \in SUBSET AllPossibleEdges  \* Random graph topology
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]
    /\ parent = [n \in Nodes |-> n]  \* Everyone points to themselves initially

\* A node n can improve by adopting neighbor m as parent
\* Condition: m's distance + 1 < n's current distance
\* The new distance must be strictly between m's distance + 1 and n's current distance
CanImprove(n, m) ==
    /\ n /= Root                           \* Root doesn't change
    /\ m \in Neighbors(n)                  \* m must be a neighbor
    /\ dist[m] < MaxDist                   \* m has a finite distance
    /\ dist[m] + 1 < dist[n]               \* Strict improvement possible

\* Node n improves by adopting neighbor m as parent
Improve(n, m) ==
    /\ CanImprove(n, m)
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED edges

\* Next state: some node improves its distance
Next ==
    \E n \in Nodes : \E m \in Nodes : Improve(n, m)

\* The algorithm is quiescent when no improvement is possible
Quiescent ==
    ~\E n \in Nodes : \E m \in Nodes : CanImprove(n, m)

\* A node is reachable from root if there's a path in the graph
\* We define this inductively through the edges
ReachableFromRoot ==
    LET RECURSIVE Reachable(_)
        Reachable(S) ==
            LET NewNodes == {m \in Nodes : \E n \in S : {n, m} \in edges}
            IN IF NewNodes \subseteq S
               THEN S
               ELSE Reachable(S \cup NewNodes)
    IN Reachable({Root})

\* Check if a node has any reachable neighbors (neighbors with finite distance)
HasReachableNeighbor(n) ==
    \E m \in Neighbors(n) : dist[m] < MaxDist

\* Safety: When quiescent, the result forms a valid spanning tree for reachable nodes
\* and correctly identifies unreachable nodes

\* For reachable nodes (except root): parent is a neighbor and dist = parent's dist + 1
ValidTreeProperty ==
    \A n \in Nodes :
        (n /= Root /\ dist[n] < MaxDist) =>
            /\ parent[n] \in Neighbors(n)
            /\ dist[n] = dist[parent[n]] + 1

\* Root has distance 0 and is its own parent
RootProperty ==
    /\ dist[Root] = 0
    /\ parent[Root] = Root

\* Unreachable nodes have MaxDist and no reachable neighbors
UnreachableProperty ==
    \A n \in Nodes :
        (n \notin ReachableFromRoot) =>
            /\ dist[n] = MaxDist
            /\ ~HasReachableNeighbor(n)

\* Reachable nodes (except root) have finite distance
ReachableHaveFiniteDist ==
    \A n \in ReachableFromRoot : dist[n] < MaxDist

\* Combined safety property: when quiescent, all properties hold
Safety ==
    Quiescent =>
        /\ RootProperty
        /\ ValidTreeProperty
        /\ UnreachableProperty
        /\ ReachableHaveFiniteDist

\* Invariant that always holds: distances are consistent
DistanceConsistency ==
    /\ dist[Root] = 0
    /\ \A n \in Nodes : 
        (dist[n] < MaxDist /\ n /= Root) => 
            /\ parent[n] \in Neighbors(n)
            /\ dist[n] = dist[parent[n]] + 1

\* Liveness: The algorithm eventually reaches quiescent state
Liveness == <>Quiescent

\* Fairness: We need weak fairness on improvements to ensure progress
Fairness ==
    \A n \in Nodes : \A m \in Nodes :
        WF_vars(Improve(n, m))

\* The complete specification
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\* Termination detection (alternative form)
Terminated == Quiescent /\ ENABLED(Next) = FALSE

\* Additional invariant: distances never increase
DistanceMonotonic ==
    [][
        \A n \in Nodes : dist'[n] <= dist[n]
    ]_vars

\* The spanning tree is valid when algorithm terminates
SpanningTreeValid ==
    Quiescent =>
        \A n \in ReachableFromRoot \ {Root} :
            /\ parent[n] \in ReachableFromRoot
            /\ {n, parent[n]} \in edges
            /\ dist[n] = dist[parent[n]] + 1

=============================================================================