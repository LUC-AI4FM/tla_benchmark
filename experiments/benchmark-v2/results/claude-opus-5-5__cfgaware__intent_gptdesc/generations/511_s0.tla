---------------------------- MODULE BFSDepth ----------------------------
(***************************************************************************)
(* Distributed computation of hop-distances (depths) from a root node in a *)
(* connected undirected network.  Channels are asynchronous, unordered and *)
(* lossless (modelled as a set of in-transit messages).  Each node keeps a *)
(* depth estimate (MaxNodes plays the role of "infinity") and a parent     *)
(* pointer.  A node whose parent pointer is itself has no parent; the root *)
(* never selects a parent.                                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,      \* finite set of nodes
          Edges,      \* set of pairs <<a, b>>; treated as undirected
          root,       \* designated root node
          MaxNodes    \* bound on depths, >= Cardinality(Nodes)

ASSUME /\ root \in Nodes
       /\ Edges \subseteq (Nodes \X Nodes)
       /\ MaxNodes \in Nat
       /\ MaxNodes >= Cardinality(Nodes)

VARIABLES depth,   \* depth[n] : current depth estimate of n
          parent,  \* parent[n] : next hop toward root (n itself = none)
          msgs     \* set of messages in transit

vars == <<depth, parent, msgs>>

Infinity == MaxNodes

Nbrs(n) == { m \in Nodes : <<n, m>> \in Edges \/ <<m, n>> \in Edges }

Msg == [from : Nodes, to : Nodes, d : 0..MaxNodes]

(***************************************************************************)
(* Graph distances, computed by breadth-first layering.                    *)
(***************************************************************************)
Reach[k \in 0..MaxNodes] ==
    IF k = 0 THEN {root}
    ELSE Reach[k-1] \cup UNION { Nbrs(m) : m \in Reach[k-1] }

Dist(n) ==
    IF \E k \in 0..MaxNodes : n \in Reach[k]
    THEN CHOOSE k \in 0..MaxNodes :
             /\ n \in Reach[k]
             /\ \A j \in 0..MaxNodes : j < k => n \notin Reach[j]
    ELSE Infinity

Connected == \A n \in Nodes : n \in Reach[MaxNodes]

(***************************************************************************)
(* Initial state: root has depth 0 and announces it to its neighbours.     *)
(***************************************************************************)
Init ==
    /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE Infinity]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = { [from |-> root, to |-> k, d |-> 0] : k \in Nbrs(root) }

(***************************************************************************)
(* Receive a message (any message: arbitrary reordering).  If it improves  *)
(* the receiver's estimate, adopt the sender as parent and broadcast the   *)
(* new depth to all neighbours.                                            *)
(***************************************************************************)
Receive(m) ==
    /\ m \in msgs
    /\ LET n    == m.to
           newd == m.d + 1
       IN IF newd < depth[n]
          THEN /\ depth'  = [depth EXCEPT ![n] = newd]
                /\ parent' = [parent EXCEPT ![n] = m.from]
                /\ msgs'   = (msgs \ {m}) \cup
                             { [from |-> n, to |-> k, d |-> newd] : k \in Nbrs(n) }
          ELSE /\ msgs' = msgs \ {m}
                /\ UNCHANGED <<depth, parent>>

\* Quiescence: nothing left to do; stutter to avoid a spurious deadlock.
Done ==
    /\ msgs = {}
    /\ UNCHANGED vars

Next == (\E m \in msgs : Receive(m)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E m \in msgs : Receive(m))

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ depth  \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs   \subseteq Msg

\* Root always has depth 0 and never selects a parent.
RootOK ==
    /\ depth[root] = 0
    /\ parent[root] = root

\* Depths are bounded and never below the true distance.
DepthBounded ==
    \A n \in Nodes : depth[n] \in 0..MaxNodes /\ depth[n] >= Dist(n)

\* Message content constraints: sent along an edge, carrying a depth no
\* less than the sender's current depth.
MsgOK ==
    \A m \in msgs :
        /\ m.to \in Nbrs(m.from)
        /\ m.d >= depth[m.from]
        /\ m.d < MaxNodes

\* Parent pointers of non-root nodes point to neighbours.
ParentOK ==
    \A n \in Nodes \ {root} :
        parent[n] # n => parent[n] \in Nbrs(n)

Safety == TypeOK /\ RootOK /\ DepthBounded /\ MsgOK /\ ParentOK

Quiescent == msgs = {}

\* Postcondition: once quiescent, depths are graph distances and parent
\* pointers form shortest-path routes to the root.
DepthCorrect ==
    (Quiescent /\ Connected) =>
        \A n \in Nodes :
            /\ depth[n] = Dist(n)
            /\ n # root =>
                  /\ parent[n] \in Nbrs(n)
                  /\ depth[parent[n]] = depth[n] - 1

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>[](msgs = {})

EventuallyCorrect ==
    <>[](Quiescent /\ \A n \in Nodes : Connected => depth[n] = Dist(n))

=============================================================================