---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

\* Generate random edges: for each node, pick a random subset of other nodes
\* This creates an undirected graph
EdgesFrom(n) == RandomElement(SUBSET (Nodes \ {n}))

\* Store the randomly generated edges for each node
VARIABLES mom, dist, edges

vars == <<mom, dist, edges>>

\* Initialize edges as a random undirected graph
InitEdges == [n \in Nodes |-> EdgesFrom(n)]

\* The set of neighbors of node n in the undirected graph
Neighbors(n) == edges[n] \cup {m \in Nodes : n \in edges[m]}

\* Type correctness invariant
TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat \cup {-1}]
    /\ edges \in [Nodes -> SUBSET Nodes]

\* A node is reachable if it has a non-negative distance
Reachable(n) == dist[n] >= 0

\* Infinity represented as -1 for unreachable nodes
Infinity == -1

\* Initial state
Init ==
    /\ edges = InitEdges
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

\* A node n can adopt neighbor m as parent if m has strictly smaller distance
\* and n either has no path yet or can improve its distance
CanAdopt(n, m) ==
    /\ m \in Neighbors(n)
    /\ dist[m] >= 0
    /\ \/ dist[n] = Infinity
       \/ dist[m] < dist[n] - 1

\* Node n adopts neighbor m as parent, choosing some intermediate distance
Adopt(n, m) ==
    /\ CanAdopt(n, m)
    /\ mom' = [mom EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ edges' = edges

\* The Next action: some node adopts a neighbor with strictly smaller distance
Next ==
    \E n \in Nodes : \E m \in Nodes :
        /\ n # Root
        /\ Adopt(n, m)

\* A node has converged if it's either:
\* - The root (distance 0, parent is self)
\* - Has found a path (parent is a neighbor with distance one less)
\* - Is unreachable (no neighbor has a finite distance)
NodeConverged(n) ==
    \/ (n = Root /\ dist[n] = 0 /\ mom[n] = Root)
    \/ (n # Root /\ dist[n] > 0 /\ mom[n] \in Neighbors(n) /\ dist[mom[n]] = dist[n] - 1)
    \/ (n # Root /\ dist[n] = Infinity /\ \A m \in Neighbors(n) : dist[m] = Infinity)

\* Postcondition: characterizes a rooted spanning-tree or unreachable nodes
Postcondition ==
    \A n \in Nodes : NodeConverged(n)

\* The system is quiescent when no node can improve
Quiescent ==
    ~(\E n \in Nodes : \E m \in Nodes : n # Root /\ CanAdopt(n, m))

\* Safety: quiescence implies postcondition
SafetyProperty ==
    Quiescent => Postcondition

\* Liveness: eventually the postcondition holds
LivenessProperty ==
    <>Postcondition

\* The specification with weak fairness on Next
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

\* Properties to check
THEOREM Spec => []TypeOK
THEOREM Spec => []SafetyProperty
THEOREM Spec => LivenessProperty

=============================================================================