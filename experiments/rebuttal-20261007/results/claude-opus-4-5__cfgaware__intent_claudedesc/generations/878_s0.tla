--------------------------- MODULE SpanningTree ---------------------------

CONSTANTS Nodes, Edges, Root, MaxDist

VARIABLES dist, parent

vars == <<dist, parent>>

\* Helper: Get neighbors of a node
Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

\* Type invariant
TypeOK == 
    /\ dist \in [Nodes -> 0..MaxDist]
    /\ parent \in [Nodes -> Nodes]

\* Initial state
Init == 
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]
    /\ parent = [n \in Nodes |-> n]

\* A node can improve its distance if it has a neighbor with smaller distance
CanImprove(n) == 
    \E m \in Neighbors(n) : dist[n] > dist[m] + 1

\* Node n improves its distance based on neighbor m
Improve(n, m) == 
    /\ m \in Neighbors(n)
    /\ dist[n] > dist[m] + 1
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ parent' = [parent EXCEPT ![n] = m]

\* Next state: some node improves its distance
Next == \E n \in Nodes : \E m \in Neighbors(n) : Improve(n, m)

\* Termination condition: no node can improve
Terminated == ~(\E n \in Nodes : CanImprove(n))

\* Fairness: if improvement is possible, it eventually happens
Fairness == WF_vars(Next)

\* Full specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Reachability: nodes reachable from root via edges
Reachable == 
    LET RECURSIVE ReachableFrom(_)
        ReachableFrom(S) == 
            LET NewNodes == S \cup UNION {Neighbors(n) : n \in S}
            IN IF NewNodes = S THEN S ELSE ReachableFrom(NewNodes)
    IN ReachableFrom({Root})

\* Safety property: upon termination, parent function encodes valid spanning tree
Safety == 
    Terminated => 
        /\ dist[Root] = 0
        /\ parent[Root] = Root
        /\ \A n \in Nodes :
            IF n \in Reachable THEN
                \* Reachable nodes form a valid tree
                IF n = Root THEN
                    TRUE
                ELSE
                    /\ parent[n] \in Neighbors(n)
                    /\ dist[n] = dist[parent[n]] + 1
            ELSE
                \* Unreachable nodes retain MaxDist and are their own parent
                /\ dist[n] = MaxDist
                /\ parent[n] = n
                /\ \A m \in Neighbors(n) : dist[m] >= dist[n]

\* Liveness property: algorithm eventually terminates
Liveness == <>Terminated

=============================================================================