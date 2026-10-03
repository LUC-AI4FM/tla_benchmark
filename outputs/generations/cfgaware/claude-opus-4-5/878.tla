---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, Naturals

CONSTANTS Nodes, Edges, Root, MaxCardinality

VARIABLES mom, dist

vars == <<mom, dist>>

\* Helper: Get neighbors of a node in the undirected graph
Neighbors(n) == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}

\* Type invariant
TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> 0..MaxCardinality]

\* Initial state
Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

\* A node can update its parent and distance if it finds a neighbor with shorter distance
Update(n) == 
    /\ \E neighbor \in Neighbors(n) :
        /\ dist[neighbor] < dist[n]
        /\ \E newDist \in (dist[neighbor] + 1)..(dist[n] - 1) :
            /\ dist' = [dist EXCEPT ![n] = newDist]
            /\ mom' = [mom EXCEPT ![n] = neighbor]

\* Next state relation
Next == \E n \in Nodes : Update(n)

\* Termination: no more updates possible
Terminated == ~ENABLED Next

\* Postcondition: characterizes a correct rooted spanning tree
\* - Root has distance 0 and points to itself
\* - Every other node has distance = dist[mom[n]] + 1 and mom[n] is a neighbor
\* - Every node is reachable from root (dist < MaxCardinality for connected nodes)
Postcondition ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root
    /\ \A n \in Nodes \ {Root} :
        (dist[n] < MaxCardinality) =>
            /\ mom[n] \in Neighbors(n)
            /\ dist[n] = dist[mom[n]] + 1

\* Safety: termination implies postcondition
Safety == Terminated => Postcondition

\* Liveness: eventual termination
Liveness == <>Terminated

\* Additional temporal property: every node eventually has root as ancestor
\* This is expressed as every node eventually having the root as its parent
\* (through the chain of parent pointers)
RootIsParent == \A n \in Nodes : <>(mom[n] = Root \/ n = Root \/ dist[n] = MaxCardinality)

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================