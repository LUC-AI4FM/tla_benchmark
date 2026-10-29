---------------------------- MODULE DistributedBFS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,     \* set of nodes
          Edges,     \* set of edges, each a pair <<a, b>> (treated as undirected)
          root,      \* designated root node
          MaxNodes   \* upper bound on depth (acts as "infinity")

ASSUME root \in Nodes
ASSUME MaxNodes \in Nat
ASSUME Edges \subseteq (Nodes \X Nodes)

VARIABLES depth,   \* depth[n]: current best-known distance of n from root
          parent,  \* parent[n]: current parent of n in the tree
          msgs     \* msgs[<<a,b>>]: FIFO queue of depth values sent from a to b

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
\* Directed channels: one queue per direction of every undirected edge
DEdges == { <<a, b>> \in Nodes \X Nodes :
              <<a, b>> \in Edges \/ <<b, a>> \in Edges }

Neighbors(n) == { m \in Nodes : <<n, m>> \in DEdges }

\* A queue holds strictly decreasing depth values (a sender only re-announces
\* when its depth strictly improves).
Ordered(q) == \A i, j \in DOMAIN q : i < j => q[i] > q[j]

TypeOK ==
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs \in [DEdges -> Seq(0..MaxNodes)]
    /\ \A e \in DEdges : Ordered(msgs[e])

-----------------------------------------------------------------------------
Init ==
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs = [e \in DEdges |-> IF e[1] = root THEN <<0>> ELSE <<>>]

\* Node n receives a depth announcement d from neighbor m.
Receive(m, n) ==
    /\ <<m, n>> \in DEdges
    /\ msgs[<<m, n>>] # <<>>
    /\ LET d == Head(msgs[<<m, n>>]) IN
         IF d + 1 < depth[n]
           THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
                /\ parent' = [parent EXCEPT ![n] = m]
                /\ msgs' = [e \in DEdges |->
                              IF e = <<m, n>>
                                THEN IF e[1] = n
                                       THEN Append(Tail(msgs[e]), d + 1)
                                       ELSE Tail(msgs[e])
                              ELSE IF e[1] = n
                                THEN Append(msgs[e], d + 1)
                              ELSE msgs[e]]
           ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = Tail(@)]
                /\ UNCHANGED <<depth, parent>>

Terminated == \A e \in DEdges : msgs[e] = <<>>

Done == Terminated /\ UNCHANGED vars

Next == (\E e \in DEdges : Receive(e[1], e[2])) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Graph-theoretic shortest distance from root
RECURSIVE Reach(_)
Reach(k) == IF k = 0 THEN {root}
            ELSE Reach(k - 1) \cup
                 { m \in Nodes : \E n \in Reach(k - 1) : <<n, m>> \in DEdges }

Dist(n) == IF \E k \in 0..MaxNodes : n \in Reach(k)
             THEN CHOOSE k \in 0..MaxNodes :
                     /\ n \in Reach(k)
                     /\ \A j \in 0..MaxNodes : j < k => n \notin Reach(j)
             ELSE MaxNodes

\* Length of the path to the root following parent pointers
RECURSIVE ParentIter(_, _)
ParentIter(k, n) == IF k = 0 THEN n ELSE parent[ParentIter(k - 1, n)]

PathLen(n) == IF \E k \in 0..MaxNodes : ParentIter(k, n) = root
                THEN CHOOSE k \in 0..MaxNodes :
                        /\ ParentIter(k, n) = root
                        /\ \A j \in 0..MaxNodes : j < k => ParentIter(j, n) # root
                ELSE MaxNodes

\* Postcondition: upon termination parent pointers form a BFS tree
DepthCorrect ==
    Terminated =>
        \A n \in Nodes : /\ PathLen(n) = Dist(n)
                         /\ depth[n] = Dist(n)

\* Liveness: the algorithm eventually terminates
Termination == <>Terminated

=============================================================================