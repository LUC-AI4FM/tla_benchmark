------------------------- MODULE DistributedShortestPathTree -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,      \* set of nodes
          Edges,      \* set of undirected edges, each a 2-element subset of Nodes
          Root,       \* the distinguished root node
          NoParent    \* value indicating "no parent"

ASSUME RootInNodes   == Root \in Nodes
ASSUME EdgesWellFormed == \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
ASSUME NoParentNotNode == NoParent \notin Nodes

N == Cardinality(Nodes)

\* Infinity sentinel: no shortest path in a connected graph is >= N
Infty == N

Nbrs(n) == {m \in Nodes : {n, m} \in Edges}

\* Ball[k] = set of nodes within k hops of Root
Ball[k \in 0..N] ==
    IF k = 0 THEN {Root}
    ELSE Ball[k-1] \cup {m \in Nodes : \E x \in Ball[k-1] : {x, m} \in Edges}

\* The graph is connected
ASSUME Connected == \A n \in Nodes : n \in Ball[N]

\* True shortest-path distance from Root
SP(n) == CHOOSE k \in 0..N : n \in Ball[k] /\ (k = 0 \/ n \notin Ball[k-1])

Messages == [src : Nodes, dst : Nodes, d : 0..N]

VARIABLES dist,    \* dist[n]: current known distance of n to Root
          parent,  \* parent[n]: neighbor on current path to Root
          msgs     \* set of in-transit messages on channels

vars == <<dist, parent, msgs>>

------------------------------------------------------------------------------------

TypeOK ==
    /\ dist \in [Nodes -> 0..N]
    /\ parent \in [Nodes -> Nodes \cup {NoParent}]
    /\ msgs \subseteq Messages
    /\ \A msg \in msgs : {msg.src, msg.dst} \in Edges

Init ==
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infty]
    /\ parent = [n \in Nodes |-> NoParent]
    /\ msgs = {[src |-> Root, dst |-> m, d |-> 0] : m \in Nbrs(Root)}

\* Node n receives a distance announcement from a neighbor
Receive(n) ==
    \E msg \in msgs :
        /\ msg.dst = n
        /\ IF msg.d + 1 < dist[n]
             THEN /\ dist' = [dist EXCEPT ![n] = msg.d + 1]
                  /\ parent' = [parent EXCEPT ![n] = msg.src]
                  /\ msgs' = (msgs \ {msg}) \cup
                             {[src |-> n, dst |-> m, d |-> msg.d + 1] :
                                 m \in Nbrs(n) \ {msg.src}}
             ELSE /\ msgs' = msgs \ {msg}
                  /\ UNCHANGED <<dist, parent>>

Stabilized == msgs = {}

\* Stuttering once stable, to avoid spurious deadlock
Done == Stabilized /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Fairness == \A n \in Nodes : WF_vars(Receive(n))

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------------
\* Safety properties

\* A node's recorded distance never underestimates the true shortest distance
NeverUnderestimate == \A n \in Nodes : dist[n] >= SP(n)

\* Distance semantics: a finite distance is justified by the parent pointer
ParentConsistent ==
    \A n \in Nodes \ {Root} :
        dist[n] < Infty =>
            /\ parent[n] \in Nbrs(n)
            /\ dist[parent[n]] + 1 <= dist[n]

RootInvariant == dist[Root] = 0

\* Correctness at stabilization
Correct ==
    /\ \A n \in Nodes : dist[n] = SP(n)
    /\ \A n \in Nodes \ {Root} :
          /\ parent[n] \in Nbrs(n)
          /\ dist[n] = dist[parent[n]] + 1

StableCorrect == Stabilized => Correct

Safety == TypeOK /\ NeverUnderestimate /\ ParentConsistent /\ RootInvariant /\ StableCorrect

\* Liveness properties
Termination == <>[]Stabilized

EventuallyCorrect == <>[]Correct

THEOREM Spec => []Safety
THEOREM Spec => Termination /\ EventuallyCorrect
====================================================================================