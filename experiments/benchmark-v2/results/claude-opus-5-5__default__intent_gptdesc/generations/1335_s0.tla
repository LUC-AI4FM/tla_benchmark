------------------------------ MODULE EchoSpanningTree ------------------------------
(***************************************************************************)
(* Asynchronous Echo algorithm for spanning-tree construction in an       *)
(* undirected, connected graph with a single designated initiator.        *)
(*                                                                         *)
(* Messages are "explore" and "ack". Channels are reliable but unordered: *)
(* messages are never lost or duplicated, and any in-flight message may   *)
(* be delivered next. Over each directed edge, at most one message is     *)
(* ever sent, so the in-flight messages form a set.                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,        \* finite set of processes
    Initiator,   \* the designated initiator
    Neighbors    \* Neighbors[n] : set of neighbors of node n

NoNode == CHOOSE x : x \notin Node

(***************************************************************************)
(* Assumptions: well-formed, undirected (symmetric, irreflexive), and     *)
(* connected graph.                                                       *)
(***************************************************************************)
ASSUME NodeFinite      == IsFiniteSet(Node) /\ Node # {}
ASSUME InitiatorInNode == Initiator \in Node
ASSUME NeighborsType   == Neighbors \in [Node -> SUBSET Node]
ASSUME Irreflexive     == \A n \in Node : n \notin Neighbors[n]
ASSUME Symmetric       == \A n, m \in Node : m \in Neighbors[n] <=> n \in Neighbors[m]
ASSUME Connected       ==
    \A S \in SUBSET Node :
        (Initiator \in S /\ S # Node) =>
            \E u \in S, v \in Node \ S : v \in Neighbors[u]

MsgType  == {"explore", "ack"}
Messages == [type : MsgType, src : Node, dst : Node]

VARIABLES
    msgs,      \* set of in-flight messages (global network state)
    started,   \* started[n]  : n has begun participating (sent its explores)
    parent,    \* parent[n]   : parent of n, or NoNode
    children,  \* children[n] : set of nodes that acknowledged n as parent
    rcvd,      \* rcvd[n]     : number of messages n has received
    done       \* done[n]     : n has completed the protocol

vars == <<msgs, started, parent, children, rcvd, done>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \subseteq Messages
    /\ started  \in [Node -> BOOLEAN]
    /\ parent   \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd     \in [Node -> 0..Cardinality(Node)]
    /\ done     \in [Node -> BOOLEAN]

\* Every message travels along an edge of the graph and has a valid type.
MsgWellFormed ==
    \A m \in msgs :
        /\ m.type \in MsgType
        /\ m.src \in Node /\ m.dst \in Node
        /\ m.src \in Neighbors[m.dst]
        /\ m.dst \in Neighbors[m.src]

\* Neighbor relation remains well formed (static, but checked as invariant).
NeighborsWellFormed ==
    \A n \in Node :
        /\ Neighbors[n] \subseteq Node
        /\ n \notin Neighbors[n]
        /\ \A m \in Neighbors[n] : n \in Neighbors[m]

-----------------------------------------------------------------------------
Init ==
    /\ msgs     = {}
    /\ started  = [n \in Node |-> FALSE]
    /\ parent   = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ rcvd     = [n \in Node |-> 0]
    /\ done     = [n \in Node |-> FALSE]

\* The initiator starts by exploring all of its neighbors.
Start ==
    /\ ~started[Initiator]
    /\ started' = [started EXCEPT ![Initiator] = TRUE]
    /\ msgs' = msgs \cup
               { [type |-> "explore", src |-> Initiator, dst |-> q] :
                     q \in Neighbors[Initiator] }
    /\ UNCHANGED <<parent, children, rcvd, done>>

\* Node n receives an arbitrary in-flight message m addressed to it.
Receive(n, m) ==
    /\ m \in msgs
    /\ m.dst = n
    /\ msgs_rest == 0 = 0   \* placeholder removed below
    /\ FALSE

\* First explore received by a non-started, non-initiator node.
RecvFirstExplore(n, m) ==
    /\ m \in msgs
    /\ m.dst = n
    /\ m.type = "explore"
    /\ ~started[n]
    /\ n # Initiator
    /\ started' = [started EXCEPT ![n] = TRUE]
    /\ parent'  = [parent  EXCEPT ![n] = m.src]
    /\ rcvd'    = [rcvd    EXCEPT ![n] = @ + 1]
    /\ msgs' = (msgs \ {m}) \cup
               { [type |-> "explore", src |-> n, dst |-> q] :
                     q \in Neighbors[n] \ {m.src} }
    /\ UNCHANGED <<children, done>>

\* Subsequent explore received by an already started node.
RecvOtherExplore(n, m) ==
    /\ m \in msgs
    /\ m.dst = n
    /\ m.type = "explore"
    /\ started[n]
    /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<started, parent, children, done>>

\* Acknowledge received: sender becomes a child.
RecvAck(n, m) ==
    /\ m \in msgs
    /\ m.dst = n
    /\ m.type = "ack"
    /\ started[n]
    /\ rcvd'     = [rcvd     EXCEPT ![n] = @ + 1]
    /\ children' = [children EXCEPT ![n] = @ \cup {m.src}]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<started, parent, done>>

Deliver(n, m) ==
    \/ RecvFirstExplore(n, m)
    \/ RecvOtherExplore(n, m)
    \/ RecvAck(n, m)

\* After hearing from every neighbor, n completes and acks its parent.
Complete(n) ==
    /\ started[n]
    /\ ~done[n]
    /\ rcvd[n] = Cardinality(Neighbors[n])
    /\ done' = [done EXCEPT ![n] = TRUE]
    /\ msgs' = IF parent[n] # NoNode
                  THEN msgs \cup {[type |-> "ack", src |-> n, dst |-> parent[n]]}
                  ELSE msgs
    /\ UNCHANGED <<started, parent, children, rcvd>>

Next ==
    \/ Start
    \/ \E n \in Node : \E m \in msgs : Deliver(n, m)
    \/ \E n \in Node : Complete(n)

Fairness ==
    /\ WF_vars(Start)
    /\ \A n \in Node : WF_vars(\E m \in msgs : Deliver(n, m))
    /\ \A n \in Node : WF_vars(Complete(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

InitiatorNoParent == parent[Initiator] = NoNode

ParentIsNeighbor ==
    \A n \in Node : parent[n] # NoNode => parent[n] \in Neighbors[n]

NonInitiatorParentIffStarted ==
    \A n \in Node \ {Initiator} : started[n] <=> parent[n] # NoNode

ChildrenConsistent ==
    \A n \in Node : \A c \in children[n] : parent[c] = n

DoneImpliesStarted == \A n \in Node : done[n] => started[n]

\* Following parent links k steps from n (stopping at a node with no parent).
RECURSIVE Ancestor(_, _)
Ancestor(n, k) ==
    IF k = 0 THEN n
    ELSE LET p == Ancestor(n, k - 1)
         IN  IF parent[p] = NoNode THEN p ELSE parent[p]

ReachesRoot(n) == \E k \in 0..Cardinality(Node) : Ancestor(n, k) = Initiator

AllDone == \A n \in Node : done[n]

\* When all nodes have completed, the parent links form a spanning tree
\* rooted at the initiator: every node has a parent except the root, and
\* every node's parent chain reaches the root (hence no cycles).
SpanningTree ==
    AllDone =>
        /\ \A n \in Node \ {Initiator} : parent[n] \in Neighbors[n]
        /\ parent[Initiator] = NoNode
        /\ \A n \in Node : ReachesRoot(n)
        /\ \A n \in Node : children[n] = {c \in Node : parent[c] = n}
        /\ msgs = {}

Invariants ==
    /\ TypeOK
    /\ MsgWellFormed
    /\ NeighborsWellFormed
    /\ InitiatorNoParent
    /\ ParentIsNeighbor
    /\ NonInitiatorParentIffStarted
    /\ ChildrenConsistent
    /\ DoneImpliesStarted
    /\ SpanningTree

-----------------------------------------------------------------------------
(* Liveness *)

EveryNodeCompletes == \A n \in Node : <>done[n]

EventuallyAllDone == <>[]AllDone

THEOREM Spec => []Invariants
THEOREM Spec => EveryNodeCompletes
=============================================================================