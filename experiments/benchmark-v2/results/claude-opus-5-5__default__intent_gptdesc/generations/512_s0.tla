------------------------------ MODULE ShortestPathSpanningTree ------------------------------
(***************************************************************************)
(* Asynchronous distributed construction of a shortest-path (BFS)          *)
(* spanning tree rooted at a distinguished node.  Channels are modeled as  *)
(* a set of in-flight messages <<from, to, d>> on directed channels, with  *)
(* no ordering.                                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,  \* finite set of nodes
          Edges,  \* set of undirected edges, each a 2-element subset of Nodes
          Root    \* distinguished root node

VARIABLES dist,   \* dist[n]   : current distance estimate of node n
          parent, \* parent[n] : current parent of n (n itself if unknown)
          msgs    \* set of in-flight messages <<sender, receiver, distance>>

vars == <<dist, parent, msgs>>

N == Cardinality(Nodes)

\* No simple path has length >= N, so N serves as "infinity".
Infinity == N

Nbrs(n) == {m \in Nodes : {n, m} \in Edges}

(***************************************************************************)
(* Graph-theoretic shortest-path distance, defined via path existence.    *)
(***************************************************************************)
PathOfLen(n, k) ==
    \E p \in [0..k -> Nodes] :
        /\ p[0] = Root
        /\ p[k] = n
        /\ \A i \in 0..(k-1) : {p[i], p[i+1]} \in Edges

SPDist(n) ==
    CHOOSE k \in 0..(N-1) :
        /\ PathOfLen(n, k)
        /\ \A j \in 0..(k-1) : ~PathOfLen(n, j)

ASSUME
    /\ IsFiniteSet(Nodes)
    /\ Root \in Nodes
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2
    /\ \A n \in Nodes : \E k \in 0..(N-1) : PathOfLen(n, k)   \* connected

(***************************************************************************)
(* Reachability of the root by following parent pointers.                  *)
(***************************************************************************)
ParentChainReachesRoot(n) ==
    \E k \in 0..(N-1) :
        \E p \in [0..k -> Nodes] :
            /\ p[0] = n
            /\ p[k] = Root
            /\ \A i \in 0..(k-1) : p[i+1] = parent[p[i]]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ dist   = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = {<<Root, m, 0>> : m \in Nbrs(Root)}

(***************************************************************************)
(* Node n receives some message addressed to it.  If the carried distance *)
(* yields an improvement, n adopts it, sets its parent to the sender, and *)
(* propagates its new distance to its other neighbors.  Otherwise the      *)
(* message is simply consumed.                                             *)
(***************************************************************************)
Receive(n) ==
    \E m \in msgs :
        /\ m[2] = n
        /\ LET s == m[1]
               d == m[3]
           IN IF d + 1 < dist[n]
                THEN /\ dist'   = [dist EXCEPT ![n] = d + 1]
                     /\ parent' = [parent EXCEPT ![n] = s]
                     /\ msgs'   = (msgs \ {m})
                                    \cup {<<n, k, d + 1>> : k \in Nbrs(n) \ {s}}
                ELSE /\ msgs'   = msgs \ {m}
                     /\ UNCHANGED <<dist, parent>>

\* Quiescence: no messages remain; allow stuttering to avoid deadlock.
Done ==
    /\ msgs = {}
    /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Receive(n))

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
    /\ dist   \in [Nodes -> 0..Infinity]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs   \subseteq (Nodes \X Nodes \X Nat)

\* Messages only travel along edges.
MsgsOnEdges == \A m \in msgs : {m[1], m[2]} \in Edges

\* The root never changes.
RootStable == dist[Root] = 0 /\ parent[Root] = Root

\* Estimates are never below the true shortest-path distance.
DistLowerBound == \A n \in Nodes : dist[n] >= SPDist(n)

\* Every message carries a value that was once the sender's distance:
\* it is no smaller than the sender's current estimate nor its true distance.
MsgValid ==
    \A m \in msgs : /\ m[3] >= dist[m[1]]
                    /\ m[3] >= SPDist(m[1])

\* Parent pointers of nodes with finite estimates point to neighbors whose
\* estimate is strictly smaller; hence parent links contain no cycles.
ParentValid ==
    \A n \in Nodes \ {Root} :
        IF dist[n] < Infinity
          THEN /\ parent[n] \in Nbrs(n)
               /\ dist[parent[n]] + 1 <= dist[n]
          ELSE parent[n] = n

\* Every node with a finite estimate reaches the root through parent links.
NoParentCycles ==
    \A n \in Nodes : dist[n] < Infinity => ParentChainReachesRoot(n)

\* When the system has quiesced, distances are exact and parent pointers
\* form a shortest-path spanning tree rooted at Root.
CorrectAtTermination ==
    (msgs = {}) =>
        /\ \A n \in Nodes : dist[n] = SPDist(n)
        /\ \A n \in Nodes \ {Root} :
               /\ parent[n] \in Nbrs(n)
               /\ dist[parent[n]] = dist[n] - 1
        /\ \A n \in Nodes : ParentChainReachesRoot(n)

Invariants ==
    /\ TypeOK
    /\ MsgsOnEdges
    /\ RootStable
    /\ DistLowerBound
    /\ MsgValid
    /\ ParentValid
    /\ NoParentCycles
    /\ CorrectAtTermination

(***************************************************************************)
(* Action properties: monotonicity and validity                            *)
(***************************************************************************)
Monotonicity ==
    [][\A n \in Nodes : dist'[n] <= dist[n]]_vars

AdoptionValidity ==
    [][\A n \in Nodes :
          dist'[n] # dist[n] =>
              /\ parent'[n] \in Nbrs(n)
              /\ <<parent'[n], n, dist'[n] - 1>> \in msgs
              /\ dist'[n] - 1 >= dist[parent'[n]]]_vars

(***************************************************************************)
(* Liveness: convergence                                                   *)
(***************************************************************************)
Quiescence == <>[](msgs = {})

DistConverges == <>[](\A n \in Nodes : dist[n] = SPDist(n))

TreeConverges ==
    <>[](\A n \in Nodes \ {Root} :
            /\ parent[n] \in Nbrs(n)
            /\ dist[parent[n]] = dist[n] - 1)

Convergence == Quiescence /\ DistConverges /\ TreeConverges

THEOREM Spec => []Invariants
THEOREM Spec => Monotonicity /\ AdoptionValidity
THEOREM Spec => Convergence
=============================================================================================