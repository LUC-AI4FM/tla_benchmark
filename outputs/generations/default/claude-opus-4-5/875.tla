---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

\* Generate random edges using TLC's RandomElement
\* For each node, choose a random subset of other nodes as neighbors
EdgesFrom(n) == RandomElement(SUBSET (Nodes \ {n}))

\* Build undirected edges: edge exists if either direction was randomly chosen
Edges == LET directed == [n \in Nodes |-> EdgesFrom(n)]
         IN {e \in (Nodes \X Nodes) : 
              /\ e[1] # e[2]
              /\ (e[2] \in directed[e[1]] \/ e[1] \in directed[e[2]])}

\* Neighbors of a node in the undirected graph
Neighbors(n) == {m \in Nodes : {n, m} \subseteq {e[1], e[2]} /\ {n, m} \in {{e[1], e[2]} : e \in Edges}}

VARIABLES mom, dist

vars == <<mom, dist>>

\* Type correctness invariant
TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat \cup {-1}]

\* Initial state: every node points to itself, only root has distance 0
Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE -1]

\* A node n can adopt a neighbor m with strictly smaller distance
\* and choose an intermediate distance value
AdoptNeighbor(n, m) ==
    /\ n # Root
    /\ dist[m] >= 0  \* m has a valid distance (reachable)
    /\ \/ dist[n] = -1  \* n is currently unreachable
       \/ dist[m] < dist[n]  \* m has strictly smaller distance
    /\ \E d \in (dist[m] + 1)..(IF dist[n] = -1 THEN dist[m] + 1 ELSE dist[n] - 1) \cup {dist[m] + 1}:
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

\* Check if m is a neighbor of n
IsNeighbor(n, m) == 
    \E e \in Edges : (e[1] = n /\ e[2] = m) \/ (e[1] = m /\ e[2] = n)

\* Next action: some node adopts a neighbor with smaller distance
Next == \E n \in Nodes : \E m \in Nodes :
            /\ IsNeighbor(n, m)
            /\ AdoptNeighbor(n, m)

\* A node is reachable if it has a valid distance
Reachable(n) == dist[n] >= 0

\* Postcondition: characterizes a rooted spanning tree or unreachable nodes
\* For reachable nodes: they form a proper tree rooted at Root
\* For unreachable nodes: they point to themselves and have distance -1
Postcondition ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root
    /\ \A n \in Nodes :
        \/ (n = Root)
        \/ (/\ Reachable(n)
            /\ IsNeighbor(n, mom[n])
            /\ dist[mom[n]] = dist[n] - 1
            /\ Reachable(mom[n]))
        \/ (/\ ~Reachable(n)
            /\ mom[n] = n
            /\ dist[n] = -1)

\* System is quiescent when no action can be taken
Quiescent == ~ENABLED Next

\* Safety property: quiescence implies postcondition
SafetyProperty == Quiescent => Postcondition

\* Liveness property: eventually the postcondition holds
LivenessProperty == <>Postcondition

\* Specification with weak fairness on Next
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================