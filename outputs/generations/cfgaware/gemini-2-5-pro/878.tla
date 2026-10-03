---- MODULE SpanningTree ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, Root, Adj

ASSUME
    /\ IsFinite(Node)
    /\ Root \in Node
    /\ \A n \in Node: Adj[n] \subseteq Node
    /\ \A n, m \in Node: m \in Adj[n] <=> n \in Adj[m]  \* Undirected graph
    /\ \A n \in Node: n \notin Adj[n]                   \* No self-loops
    \* The graph is connected
    /\ \A S \subseteq Node: (Root \in S /\ (\A n \in S, m \in Adj[n] : m \in S)) => (S = Node)

MaxCardinality == Cardinality(Node)

VARIABLES mom, dist

vars == <<mom, dist>>

TypeOK ==
    /\ mom \in [Node -> Node]
    /\ dist \in [Node -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Node |-> n]
    /\ dist = [n \in Node |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
    \E i \in Node, j \in Adj[i]:
        (* A node i can update its parent to a neighbor j if j has a
           shorter distance, allowing for a strict decrease for i. *)
        /\ dist[j] < dist[i] - 1
        (* The distance of i is updated to an arbitrary intermediate value. *)
        /\ \E d \in {dist[j] + 1 .. dist[i] - 1}:
            /\ mom' = [mom EXCEPT ![i] = j]
            /\ dist' = [dist EXCEPT ![i] = d]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == \A i \in Node, j \in Adj[i]: dist[j] >= dist[i] - 1

Postcondition ==
    \* The mom function forms a tree rooted at the Root node.
    /\ mom[Root] = Root
    /\ \A n \in Node \ {Root}: mom[n] \in Adj[n]
    /\ \A S \subseteq Node: (S /= {} /\ (\A s \in S: mom[s] \in S)) => Root \in S
    \* The distances are correct for a shortest-path tree.
    /\ dist[Root] = 0
    /\ \A n \in Node \ {Root}: dist[n] = dist[mom[n]] + 1

Safety == [](Termination => Postcondition)

Liveness == <>Termination

=============================================================================