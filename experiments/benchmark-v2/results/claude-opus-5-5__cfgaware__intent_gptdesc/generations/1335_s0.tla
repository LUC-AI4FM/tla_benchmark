------------------------------- MODULE EchoSpanningTree -------------------------------
(***************************************************************************)
(* Asynchronous construction of a spanning tree (echo algorithm) in an     *)
(* undirected connected graph, started by a single initiator.  Nodes       *)
(* exchange "explore" and "ack" messages over reliable, unordered channels.*)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

(* The set of nodes; may be overridden in the model configuration. *)
Node == {1, 2, 3, 4}

(* A value that is not a node, used for "no parent". *)
NoNode == CHOOSE x : x \notin Node

(* The designated initiator. *)
Initiator == CHOOSE n \in Node : TRUE

(* The undirected, connected communication graph (complete graph). *)
Edges == { {m, n} : m, n \in Node } \ { {n} : n \in Node }

Nbrs(n) == { m \in Node : {m, n} \in Edges }

MsgKind == {"explore", "ack"}
Message == [kind : MsgKind, from : Node, to : Node]
Status  == {"idle", "active", "done"}

VARIABLES
    msgs,      \* set of messages in flight (unordered channels)
    parent,    \* parent[n] : parent of n, or NoNode
    children,  \* children[n] : nodes that acknowledged n as their parent
    rcvd,      \* rcvd[n] : number of messages received by n
    status     \* status[n] : local control state of n

vars == <<msgs, parent, children, rcvd, status>>

---------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ rcvd = [n \in Node |-> 0]
    /\ status = [n \in Node |-> "idle"]

ExploreMsgs(n, targets) ==
    { [kind |-> "explore", from |-> n, to |-> m] : m \in targets }

(* The initiator starts by exploring all its neighbors. *)
Start ==
    /\ status[Initiator] = "idle"
    /\ status' = [status EXCEPT ![Initiator] = "active"]
    /\ msgs' = msgs \cup ExploreMsgs(Initiator, Nbrs(Initiator))
    /\ UNCHANGED <<parent, children, rcvd>>

(* An idle non-initiator receives its first explore: adopt the sender as *)
(* parent and forward explore to all other neighbors.                    *)
ReceiveFirst(n, msg) ==
    /\ n # Initiator
    /\ status[n] = "idle"
    /\ msg.kind = "explore"
    /\ parent' = [parent EXCEPT ![n] = msg.from]
    /\ status' = [status EXCEPT ![n] = "active"]
    /\ rcvd' = [rcvd EXCEPT ![n] = 1]
    /\ msgs' = (msgs \ {msg}) \cup ExploreMsgs(n, Nbrs(n) \ {msg.from})
    /\ UNCHANGED children

(* An active node receives a further message from some neighbor. *)
ReceiveOther(n, msg) ==
    /\ status[n] = "active"
    /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
    /\ children' = IF msg.kind = "ack"
                     THEN [children EXCEPT ![n] = @ \cup {msg.from}]
                     ELSE children
    /\ msgs' = msgs \ {msg}
    /\ UNCHANGED <<parent, status>>

Receive(n) ==
    \E msg \in msgs :
        /\ msg.to = n
        /\ \/ ReceiveFirst(n, msg)
           \/ ReceiveOther(n, msg)

(* Having heard from every neighbor, a node acknowledges its parent. *)
Finish(n) ==
    /\ status[n] = "active"
    /\ rcvd[n] = Cardinality(Nbrs(n))
    /\ status' = [status EXCEPT ![n] = "done"]
    /\ msgs' = IF parent[n] # NoNode
                 THEN msgs \cup {[kind |-> "ack", from |-> n, to |-> parent[n]]}
                 ELSE msgs
    /\ UNCHANGED <<parent, children, rcvd>>

AllDone == \A n \in Node : status[n] = "done"

(* Stuttering after termination to avoid reporting a deadlock. *)
Terminated == AllDone /\ UNCHANGED vars

Next ==
    \/ Start
    \/ \E n \in Node : Receive(n) \/ Finish(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Type correctness and well-formedness *)

TypeOK ==
    /\ msgs \subseteq Message
    /\ \A msg \in msgs : msg.from \in Nbrs(msg.to)
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ status \in [Node -> Status]
    /\ \A n \in Node : rcvd[n] <= Cardinality(Nbrs(n))

NeighborsWellFormed ==
    /\ \A n \in Node : n \notin Nbrs(n)
    /\ \A m, n \in Node : m \in Nbrs(n) <=> n \in Nbrs(m)

(* Safety properties *)

InitiatorNoParent == parent[Initiator] = NoNode

ParentIsNeighbor ==
    \A n \in Node : parent[n] # NoNode => parent[n] \in Nbrs(n)

ChildrenConsistent ==
    \A n \in Node : \A c \in children[n] : parent[c] = n

RECURSIVE AncestorsOf(_, _)
AncestorsOf(n, k) ==
    IF k = 0 \/ parent[n] = NoNode
      THEN {}
      ELSE {parent[n]} \cup AncestorsOf(parent[n], k - 1)

Ancestors(n) == AncestorsOf(n, Cardinality(Node))

(* Parent links are acyclic and rooted at the initiator; upon completion *)
(* they reach every node, i.e. they form a spanning tree.               *)
AncestorProperties ==
    /\ \A n \in Node : n \notin Ancestors(n)
    /\ \A n \in Node : parent[n] # NoNode => Initiator \in Ancestors(n)
    /\ AllDone =>
         \A n \in Node \ {Initiator} :
             /\ parent[n] # NoNode
             /\ Initiator \in Ancestors(n)

SpanningTree ==
    AllDone =>
      /\ InitiatorNoParent
      /\ \A n \in Node \ {Initiator} : Initiator \in Ancestors(n)
      /\ \A n \in Node : children[n] = { c \in Node : parent[c] = n }

Safety ==
    /\ TypeOK
    /\ NeighborsWellFormed
    /\ InitiatorNoParent
    /\ ParentIsNeighbor
    /\ ChildrenConsistent
    /\ AncestorProperties
    /\ SpanningTree

(* Liveness: every node eventually completes the protocol. *)
Termination == \A n \in Node : <>(status[n] = "done")

=============================================================================