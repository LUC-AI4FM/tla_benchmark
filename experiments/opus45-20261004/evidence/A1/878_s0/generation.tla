---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, root, MaxCardinality

VARIABLES mom, dist

vars == <<mom, dist>>

-----------------------------------------------------------------------------

\* Helper: Get neighbors of a node in the undirected graph
Neighbors(n) == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}

-----------------------------------------------------------------------------

\* Type invariant
TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> 0..MaxCardinality]

\* Initial state
Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxCardinality]

\* A node n can update if it has a neighbor m with smaller distance
\* and the new distance would be less than current distance
Update(n) == 
    \E m \in Neighbors(n) :
        /\ dist[m] < dist[n]
        /\ \E d \in (dist[m] + 1)..(dist[n] - 1) \cup {dist[m] + 1} :
            /\ dist' = [dist EXCEPT ![n] = d]
            /\ mom' = [mom EXCEPT ![n] = m]

\* Next state relation
Next == \E n \in Nodes : Update(n)

\* Termination: no more updates possible
Terminated == ~ENABLED Next

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

\* Postcondition: characterizes a correct rooted spanning tree
\* 1. Root has distance 0 and is its own parent
\* 2. Every other node has a parent that is a neighbor with smaller distance
\* 3. Distance of each node equals distance of parent + 1 (except root)
Postcondition ==
    /\ dist[root] = 0
    /\ mom[root] = root
    /\ \A n \in Nodes \ {root} :
        /\ mom[n] \in Neighbors(n)
        /\ dist[n] = dist[mom[n]] + 1
        /\ dist[n] < MaxCardinality

\* Safety: termination implies postcondition
Safety == Terminated => Postcondition

\* Liveness: eventual termination
Liveness == <>Terminated

\* Additional temporal property: every node eventually has root as ancestor
\* (expressed as eventually having root as parent through the chain)
EventuallyRootParent == \A n \in Nodes : <>(mom[n] = root \/ n = root)

=============================================================================