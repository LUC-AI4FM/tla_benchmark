-------------------------- MODULE SpanningTree --------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Node,         \* The set of nodes
          Root,         \* The distinguished root node
          Adj           \* The adjacency function: n \in Node |-> {v \in Node : {n,v} is an edge}

ASSUME /\ Root \in Node
       /\ \A n \in Node: Adj[n] \subseteq Node
       /\ \A n, v \in Node: v \in Adj[n] <=> n \in Adj[v] \* Undirected graph

MaxCardinality == Cardinality(Node)

VARIABLES mom, dist

vars == <<mom, dist>>

\* Type invariant for the state variables.
TypeOK == /\ mom \in [Node -> Node]
          /\ dist \in [Node -> 0..MaxCardinality]

\* The initial state of the algorithm.
Init == /\ mom = [n \in Node |-> n]
        /\ dist = [n \in Node |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ TypeOK

\* An action where a node n chooses a neighbor v with a shorter distance
\* and updates its parent (mom) and distance (dist).
Next == \E n \in Node \setminus {Root}, v \in Adj[n]:
          /\ dist[v] < dist[n]
          /\ \E d \in {i \in Int : dist[v] < i < dist[n]}:
               /\ mom' = [mom EXCEPT ![n] = v]
               /\ dist' = [dist EXCEPT ![n] = d]

\* The complete specification, assuming weak fairness on the Next action.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================