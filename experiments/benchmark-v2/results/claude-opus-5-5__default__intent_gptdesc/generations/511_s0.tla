------------------------------ MODULE BFSDepth ------------------------------
(***************************************************************************)
(* Distributed depth (hop-distance) computation from a root node in a     *)
(* connected, undirected network.                                          *)
(*                                                                         *)
(* Each node keeps a depth estimate and a parent pointer. Messages travel  *)
(* over directed channels, one for each direction of every undirected     *)
(* edge. Delivery is asynchronous and may be reordered. No message is      *)
(* lost.                                                                    *)
(*                                                                         *)
(* Each channel is modeled as a set of in-transit depth values. Two equal  *)
(* values sent on the same channel are identical messages and have the     *)
(* same effect when received, so merging them loses no information.        *)
(*                                                                         *)
(* Depth estimates only decrease. So any value a node has sent is always   *)
(* at least its current depth.                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,   \* finite set of nodes
          Edges,   \* set of undirected edges, each a 2-element subset of Nodes
          Root     \* designated root node

NoParent == CHOOSE x : x \notin Nodes

\* "Infinity" bound: no shortest path is longer than |Nodes| - 1 hops.
MaxDepth == Cardinality(Nodes)

Nbrs(n) == { m \in Nodes : {n, m} \in Edges }

\* Directed communication channels (both directions of each edge).
Channels == { c \in Nodes \X Nodes : {c[1], c[2]} \in Edges }

\* Nodes within k hops of Root.
RECURSIVE Within(_)
Within(k) == IF k = 0
               THEN {Root}
               ELSE Within(k-1) \cup
                    { n \in Nodes : \E m \in Within(k-1) : m \in Nbrs(n) }

\* Shortest-path (hop) distance from n to Root.
Dist(n) == CHOOSE k \in 0..MaxDepth :
              /\ n \in Within(k)
              /\ \A j \in 0..(k-1) : n \notin Within(j)

ASSUME /\ Root \in Nodes
       /\ IsFiniteSet(Nodes)
       /\ Edges \subseteq { e \in SUBSET Nodes : Cardinality(e) = 2 }
       /\ Within(MaxDepth) = Nodes          \* the graph is connected

VARIABLES depth,   \* depth[n] : current depth estimate of n
          parent,  \* parent[n]: neighbor that is the next hop toward Root
          toSend,  \* toSend[n]: neighbors that n must still notify
          msgs     \* msgs[c]  : depth values in transit on channel c

vars == << depth, parent, toSend, msgs >>

---------------------------------------------------------------------------
Init ==
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDepth]
  /\ parent = [n \in Nodes |-> NoParent]
  /\ toSend = [n \in Nodes |-> IF n = Root THEN Nbrs(Root) ELSE {}]
  /\ msgs   = [c \in Channels |-> {}]

\* Node n sends its current depth to neighbor m.
Send(n, m) ==
  /\ m \in toSend[n]
  /\ msgs'   = [msgs EXCEPT ![<<n, m>>] = @ \cup {depth[n]}]
  /\ toSend' = [toSend EXCEPT ![n] = @ \ {m}]
  /\ UNCHANGED << depth, parent >>

\* Node n receives depth value d from neighbor m, in any order.
Receive(n, m, d) ==
  /\ <<m, n>> \in Channels
  /\ d \in msgs[<<m, n>>]
  /\ msgs' = [msgs EXCEPT ![<<m, n>>] = @ \ {d}]
  /\ IF n # Root /\ d + 1 < depth[n]
       THEN /\ depth'  = [depth  EXCEPT ![n] = d + 1]
            /\ parent' = [parent EXCEPT ![n] = m]
            /\ toSend' = [toSend EXCEPT ![n] = Nbrs(n)]
       ELSE UNCHANGED << depth, parent, toSend >>

Quiescent ==
  /\ \A n \in Nodes : toSend[n] = {}
  /\ \A c \in Channels : msgs[c] = {}

\* Explicit stuttering once terminated, so TLC does not report a deadlock.
Terminated == Quiescent /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes, m \in Nodes : m \in Nbrs(n) /\ Send(n, m)
  \/ \E c \in Channels, d \in 0..MaxDepth : Receive(c[2], c[1], d)
  \/ Terminated

Fairness ==
  /\ \A n \in Nodes, m \in Nodes : WF_vars(Send(n, m))
  /\ \A c \in Channels, d \in 0..MaxDepth : WF_vars(Receive(c[2], c[1], d))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
  /\ depth  \in [Nodes -> 0..MaxDepth]
  /\ parent \in [Nodes -> Nodes \cup {NoParent}]
  /\ toSend \in [Nodes -> SUBSET Nodes]
  /\ \A n \in Nodes : toSend[n] \subseteq Nbrs(n)
  /\ msgs \in [Channels -> SUBSET (0..MaxDepth)]

\* Every depth is a finite integer within the bound.
DepthBounded == \A n \in Nodes : depth[n] \in 0..MaxDepth

\* The root always has depth 0 and never selects a parent.
RootInv == depth[Root] = 0 /\ parent[Root] = NoParent

\* A message in transit never carries a value below the sender's current depth.
MsgContentInv ==
  \A c \in Channels : \A d \in msgs[c] : d \in 0..MaxDepth /\ d >= depth[c[1]]

\* No estimate is ever below the true distance.
DepthLowerBound == \A n \in Nodes : depth[n] >= Dist(n)

\* A parent pointer always names a neighbor that is strictly closer by its estimate.
ParentInv ==
  \A n \in Nodes \ {Root} :
     parent[n] # NoParent =>
        /\ parent[n] \in Nbrs(n)
        /\ depth[parent[n]] + 1 <= depth[n]

\* Depths and parent pointers that match shortest-path routes.
DepthsCorrect == \A n \in Nodes : depth[n] = Dist(n)

ParentsCorrect ==
  \A n \in Nodes \ {Root} :
     /\ parent[n] \in Nbrs(n)
     /\ Dist(parent[n]) = Dist(n) - 1

\* Postcondition: a quiescent state has correct depths and shortest-path parents.
Postcondition == Quiescent => (DepthsCorrect /\ ParentsCorrect)

Safety ==
  /\ TypeOK
  /\ DepthBounded
  /\ RootInv
  /\ MsgContentInv
  /\ DepthLowerBound
  /\ ParentInv
  /\ Postcondition

---------------------------------------------------------------------------
(* Liveness properties *)

\* Convergence: the system eventually becomes quiescent and stays quiescent.
Termination == <>[]Quiescent

\* Depths and parent pointers eventually become correct and stay correct.
EventuallyCorrect == <>[](DepthsCorrect /\ ParentsCorrect)

\* Once quiescent, the system stays quiescent.
QuiescenceStable == [](Quiescent => []Quiescent)

---------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Termination /\ EventuallyCorrect /\ QuiescenceStable
=============================================================================