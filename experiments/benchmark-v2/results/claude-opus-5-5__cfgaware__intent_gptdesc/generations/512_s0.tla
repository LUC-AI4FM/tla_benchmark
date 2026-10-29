---------------------------- MODULE ShortestPathTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,     \* the fixed set of nodes
          Edges,     \* set of undirected edges, each a 2-element set {a, b}
          root,      \* the distinguished root node
          MaxNodes   \* upper bound used as "infinity" (>= number of nodes)

VARIABLES depth,   \* depth[n] : current distance estimate of node n
          parent,  \* parent[n] : current parent of node n (n itself = unknown)
          msgs     \* msgs[<<a,b>>] : set of distance values in transit from a to b

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
SetNbrs(n) == {m \in Nodes : m # n /\ {n, m} \in Edges}

\* Directed channels, one per direction of each undirected edge
Queues == {<<a, b>> \in Nodes \X Nodes : b \in SetNbrs(a)}

Infinity == MaxNodes

TypeOK ==
  /\ depth \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs \in [Queues -> SUBSET (0..MaxNodes)]

-----------------------------------------------------------------------------
Init ==
  /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE Infinity]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs = [q \in Queues |-> IF q[1] = root THEN {0} ELSE {}]

\* Node n processes a message with distance d received from neighbor m
Receive(n, m) ==
  /\ <<m, n>> \in Queues
  /\ \E d \in msgs[<<m, n>>] :
       IF d + 1 < depth[n]
         THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ msgs' = [q \in Queues |->
                            IF q = <<m, n>> THEN msgs[q] \ {d}
                            ELSE IF q[1] = n /\ q[2] # m THEN msgs[q] \cup {d + 1}
                            ELSE msgs[q]]
         ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = @ \ {d}]
              /\ UNCHANGED <<depth, parent>>

Done == \A q \in Queues : msgs[q] = {}

Next ==
  \/ \E n \in Nodes : \E m \in SetNbrs(n) : Receive(n, m)
  \/ (Done /\ UNCHANGED vars)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes : \A m \in SetNbrs(n) : WF_vars(Receive(n, m))

-----------------------------------------------------------------------------
\* Graph-theoretic shortest distances (specification-level only)
Reach[k \in 0..MaxNodes] ==
  IF k = 0 THEN {root}
  ELSE Reach[k-1] \cup UNION {SetNbrs(x) : x \in Reach[k-1]}

ShortestDist(n) ==
  CHOOSE k \in 0..MaxNodes : n \in Reach[k] /\ \A j \in 0..MaxNodes : j < k => n \notin Reach[j]

\* Nodes reachable from n by following parent pointers
AncestorChain(n) ==
  LET A[k \in 0..MaxNodes] == IF k = 0 THEN {n} ELSE A[k-1] \cup {parent[x] : x \in A[k-1]}
  IN A[MaxNodes]

-----------------------------------------------------------------------------
\* Safety: estimates are never below the true distance and are always valid
DepthLowerBound == \A n \in Nodes : depth[n] >= ShortestDist(n)

ParentValid ==
  \A n \in Nodes \ {root} :
     depth[n] < Infinity =>
        /\ parent[n] \in SetNbrs(n)
        /\ depth[parent[n]] < depth[n]

RootFixed == depth[root] = 0 /\ parent[root] = root

\* Final correctness once no messages remain
FinalCorrect ==
  Done =>
    /\ \A n \in Nodes : depth[n] = ShortestDist(n)
    /\ \A n \in Nodes \ {root} : parent[n] \in SetNbrs(n)
                                  /\ depth[parent[n]] + 1 = depth[n]
    /\ \A n \in Nodes : root \in AncestorChain(n)

Inv == TypeOK /\ DepthLowerBound /\ ParentValid /\ RootFixed /\ FinalCorrect

\* Monotonicity: distances never increase; adopted distance is 1 + a neighbor's value
Monotone ==
  [][\A n \in Nodes : depth'[n] <= depth[n]]_vars

AdoptValid ==
  [][\A n \in Nodes :
       depth'[n] # depth[n] =>
         /\ parent'[n] \in SetNbrs(n)
         /\ depth'[n] - 1 \in msgs[<<parent'[n], n>>]]_vars

\* Liveness: eventually all distances correct and no messages in transit
Convergence ==
  <>[](Done /\ \A n \in Nodes : depth[n] = ShortestDist(n))

=============================================================================