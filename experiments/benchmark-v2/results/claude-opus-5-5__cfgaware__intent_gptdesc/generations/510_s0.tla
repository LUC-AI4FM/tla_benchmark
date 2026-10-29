---------------------------- MODULE DistanceTree ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,     \* set of nodes
          Edges,     \* set of undirected edges, each a 2-element set {a, b}
          root,      \* the designated root node
          MaxNodes   \* sentinel for "unknown" distance (>= number of nodes)

ASSUME root \in Nodes
ASSUME MaxNodes \in Nat
ASSUME \A e \in Edges : e \subseteq Nodes

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
\* Neighbors of a node in the undirected graph
SetNbrs(n) == {m \in Nodes : m # n /\ {n, m} \in Edges}

\* One FIFO queue per ordered neighbor pair <<from, to>>
Queues == {<<a, b>> \in Nodes \X Nodes : b \in SetNbrs(a)}

\* Graph-theoretic shortest-path distance to the root (BFS layers)
RECURSIVE Layer(_)
Layer(k) == IF k = 0 THEN {root}
            ELSE Layer(k-1) \cup
                 {n \in Nodes : \E m \in Layer(k-1) : m \in SetNbrs(n)}

Dist(n) == IF \E k \in 0..MaxNodes : n \in Layer(k)
           THEN CHOOSE k \in 0..MaxNodes : n \in Layer(k) /\
                    \A j \in 0..MaxNodes : n \in Layer(j) => k <= j
           ELSE MaxNodes

-----------------------------------------------------------------------------
TypeOK ==
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs \in [Queues -> Seq(0..MaxNodes)]

Init ==
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    \* The root announces its distance 0 to all of its neighbors
    /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE <<>>]

\* Node n receives the head message on the queue from neighbor m
Receive(n, m) ==
    /\ <<m, n>> \in Queues
    /\ msgs[<<m, n>>] # <<>>
    /\ LET d == Head(msgs[<<m, n>>])
           rest == [msgs EXCEPT ![<<m, n>>] = Tail(@)]
       IN IF d + 1 < depth[n]
          THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
               /\ parent' = [parent EXCEPT ![n] = m]
               \* send new distance to all neighbors except the supplier
               \* (sending to m as well would also be correct)
               /\ msgs' = [q \in Queues |->
                             IF q[1] = n /\ q[2] # m
                             THEN Append(rest[q], d + 1)
                             ELSE rest[q]]
          ELSE /\ msgs' = rest
               /\ UNCHANGED <<depth, parent>>

Next == \E q \in Queues : Receive(q[2], q[1])

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A q \in Queues : WF_vars(Receive(q[2], q[1]))

-----------------------------------------------------------------------------
\* Correctness properties

Converged == \A n \in Nodes : depth[n] = Dist(n)

Convergence == <>[]Converged

ParentValid ==
    \A n \in Nodes \ {root} :
        depth[n] < MaxNodes =>
            /\ parent[n] \in SetNbrs(n)
            /\ depth[parent[n]] <= depth[n] - 1

FinalParentValid ==
    Converged =>
        \A n \in Nodes \ {root} :
            depth[n] < MaxNodes =>
                /\ parent[n] \in SetNbrs(n)
                /\ depth[parent[n]] = depth[n] - 1

DepthLowerBound == \A n \in Nodes : depth[n] >= Dist(n)

DepthNeverIncreases ==
    [][\A n \in Nodes : depth'[n] <= depth[n]]_vars

FinalStable ==
    [][\A n \in Nodes : depth[n] = Dist(n) => depth'[n] = depth[n]]_vars

QueuesEventuallyEmpty == <>[](\A q \in Queues : msgs[q] = <<>>)

=============================================================================