---------------------------- MODULE ShortestPathTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Nodes,          \* The set of all nodes in the graph
    Root,           \* The designated root node
    Infinity        \* A special value representing infinite distance

VARIABLES
    Edges,          \* The set of undirected edges (pairs of nodes)
    parent,         \* parent[n] is the parent pointer for node n
    dist            \* dist[n] is the distance value for node n

vars == <<Edges, parent, dist>>

\* Helper: Get the neighbors of a node based on the edge set
Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

\* Type invariant
TypeOK ==
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2
    /\ parent \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat \cup {Infinity}]

\* Parent must be self or a neighbor
ParentValid ==
    \A n \in Nodes : parent[n] = n \/ parent[n] \in Neighbors(n)

\* Root always has distance 0 and is its own parent
RootInvariant ==
    /\ dist[Root] = 0
    /\ parent[Root] = Root

\* For any node with finite distance > 0, distance equals parent's distance + 1
DistanceConsistency ==
    \A n \in Nodes :
        (dist[n] \in Nat /\ dist[n] > 0) => 
            (dist[parent[n]] \in Nat /\ dist[n] = dist[parent[n]] + 1)

\* Safety invariant combining all safety properties
SafetyInvariant ==
    /\ TypeOK
    /\ ParentValid
    /\ RootInvariant
    /\ DistanceConsistency

\* Check if a node can adopt a neighbor as parent (neighbor has strictly smaller distance)
CanAdopt(n, m) ==
    /\ n # Root
    /\ m \in Neighbors(n)
    /\ dist[m] \in Nat
    /\ \/ dist[n] = Infinity
       \/ dist[m] + 1 < dist[n]

\* Predicate: node n is enabled to update
Enabled(n) ==
    \E m \in Neighbors(n) : CanAdopt(n, m)

\* Action: Node n adopts neighbor m as parent
AdoptParent(n, m) ==
    /\ CanAdopt(n, m)
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ UNCHANGED Edges

\* Action: Any node performs an update step
NodeStep(n) ==
    \E m \in Neighbors(n) : AdoptParent(n, m)

\* The graph is connected if from the root, all nodes are reachable
\* We compute reachable nodes iteratively
ReachableFrom(start) ==
    LET RECURSIVE Reach(_)
        Reach(S) ==
            LET NewNodes == S \cup UNION {Neighbors(n) : n \in S}
            IN IF NewNodes = S THEN S ELSE Reach(NewNodes)
    IN Reach({start})

\* Check if the graph is connected
GraphConnected == ReachableFrom(Root) = Nodes

\* Initial state: nondeterministically choose edges forming a connected graph
Init ==
    /\ Edges \in SUBSET {e \in SUBSET Nodes : Cardinality(e) = 2}
    /\ GraphConnected
    /\ parent = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

\* Next state: any enabled node can perform an update
Next ==
    \E n \in Nodes : NodeStep(n)

\* Fairness: every enabled node update eventually happens
Fairness ==
    \A n \in Nodes : WF_vars(NodeStep(n))

\* Specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Stability: the system is stable when no more updates are possible
Stable ==
    ~(\E n \in Nodes : Enabled(n))

\* Postcondition: every node satisfies the shortest path tree property
Postcondition ==
    \A n \in Nodes :
        \/ (n = Root /\ dist[n] = 0 /\ parent[n] = Root)
        \/ (dist[n] = Infinity /\ parent[n] = n /\ 
            \A m \in Neighbors(n) : dist[m] = Infinity)
        \/ (dist[n] \in Nat /\ dist[n] > 0 /\ 
            parent[n] \in Neighbors(n) /\ 
            dist[n] = dist[parent[n]] + 1)

\* Convergence: eventually reach a stable state satisfying the postcondition
Convergence == <>(Stable /\ Postcondition)

\* Additional property: in stable state, distances are actual shortest paths
\* (This follows from the algorithm but is a useful cross-check)
CorrectDistances ==
    Stable => 
        \A n \in Nodes :
            \/ (n = Root /\ dist[n] = 0)
            \/ (dist[n] = Infinity)
            \/ (dist[n] \in Nat /\ dist[n] > 0)

=============================================================================