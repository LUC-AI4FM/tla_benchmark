------------------------------- MODULE Echo -------------------------------
(***************************************************************************)
(* The Echo algorithm builds a spanning tree of an undirected, connected   *)
(* graph, starting from a single initiator. The initiator sends an "m"     *)
(* message to all of its neighbors. When a non-initiator node receives its *)
(* first message, it records the sender as its parent and forwards "m"     *)
(* messages to all of its other neighbors. When a node has received a      *)
(* message from every neighbor, it sends a "c" message to its parent, and  *)
(* the parent records the sender as a child. The algorithm terminates when *)
(* the initiator has received messages from all of its neighbors.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, which becomes the root of the tree
          R          \* neighborhood relation, a Boolean function over pairs of nodes

(***************************************************************************)
(* Properties of binary relations represented as Boolean functions.        *)
(***************************************************************************)
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

RECURSIVE ReachFrom(_, _, _)
ReachFrom(rel, S, T) ==
    LET U == T \cup {y \in S : \E x \in T : rel[x, y]}
    IN  IF U = T THEN T ELSE ReachFrom(rel, S, U)

IsConnected(rel, S) == \A x \in S : ReachFrom(rel, S, {x}) = S

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       \* no self-loops
       /\ IsIrreflexive(R, Node)
       \* undirected graph
       /\ IsSymmetric(R, Node)
       \* the graph is connected, so a spanning tree of all nodes exists
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];

    define {
        \* send message msg from node i to node j
        send(box, i, j, msg) == [box EXCEPT ![j] = @ \cup {msg}]
        \* send message msg from node i to all nodes in set M
        multicast(box, i, M, msg) ==
            [j \in Node |-> IF j \in M THEN box[j] \cup {msg} ELSE box[j]]
    }

    process (node \in Node)
        variables parent = NoNode, children = {}, rcvd = 0,
                  nbrs = neighbors(self); {
    n0: if (self = initiator) {
            \* the initiator sends the first message to all its neighbors
            inbox := multicast(inbox, self, nbrs, [kind |-> "m", sndr |-> self])
        };
    n1: while (rcvd < Cardinality(nbrs)) {
            \* receive some message from a neighbor
            with (msg \in inbox[self],
                  net = [inbox EXCEPT ![self] = @ \ {msg}]) {
                rcvd := rcvd + 1;
                if (self # initiator /\ rcvd = 1) {
                    \* the first message received is always of kind "m"
                    assert(msg.kind = "m");
                    \* record sender as parent and inform the other neighbors
                    parent := msg.sndr;
                    inbox := multicast(net, self, nbrs \ {msg.sndr},
                                       [kind |-> "m", sndr |-> self])
                } else {
                    \* subsequent messages are not forwarded
                    inbox := net
                };
                if (msg.kind = "c") { children := children \cup {msg.sndr} }
            }
        };
    n2: if (self # initiator) {
            \* all neighbors have answered: report to the parent
            assert(parent \in nbrs);
            inbox := send(inbox, self, parent, [kind |-> "c", sndr |-> self])
        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inbox, pc

(* define statement *)
send(box, i, j, msg) == [box EXCEPT ![j] = @ \cup {msg}]

multicast(box, i, M, msg) ==
    [j \in Node |-> IF j \in M THEN box[j] \cup {msg} ELSE box[j]]

VARIABLES parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ inbox = [n \in Node |-> {}]
        (* Process node *)
        /\ parent = [self \in Node |-> NoNode]
        /\ children = [self \in Node |-> {}]
        /\ rcvd = [self \in Node |-> 0]
        /\ nbrs = [self \in Node |-> neighbors(self)]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF self = initiator
                  THEN /\ inbox' = multicast(inbox, self, nbrs[self],
                                             [kind |-> "m", sndr |-> self])
                  ELSE /\ TRUE
                       /\ UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            LET net == [inbox EXCEPT ![self] = @ \ {msg}] IN
                            /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                            /\ IF self # initiator /\ rcvd'[self] = 1
                                  THEN /\ Assert(msg.kind = "m",
                                                 "Failure of assertion at line n1: first message must be of kind m.")
                                       /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                       /\ inbox' = multicast(net, self, nbrs[self] \ {msg.sndr},
                                                             [kind |-> "m", sndr |-> self])
                                  ELSE /\ inbox' = net
                                       /\ UNCHANGED parent
                            /\ IF msg.kind = "c"
                                  THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED children
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ Assert(parent[self] \in nbrs[self],
                                 "Failure of assertion at line n2: parent must be a neighbor.")
                       /\ inbox' = send(inbox, self, parent[self],
                                        [kind |-> "c", sndr |-> self])
                  ELSE /\ TRUE
                       /\ UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
Message == [kind : {"m", "c"}, sndr : Node]

TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]
    /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])
    /\ inbox \in [Node -> SUBSET Message]
    /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]

(* The initiator never has a parent. *)
InitiatorNoParent == parent[initiator] = NoNode

(* Any parent of a node is a neighbor of that node. *)
ParentNeighbor ==
    \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

(* Every child of a node has that node as its parent. *)
ParentChild ==
    \A n \in Node : \A c \in children[n] : parent[c] = n

(* Set of ancestors of node n obtained by following parent pointers. *)
RECURSIVE AncestorsAcc(_, _)
AncestorsAcc(n, S) ==
    IF parent[n] = NoNode \/ parent[n] \in S
    THEN S
    ELSE AncestorsAcc(parent[n], S \cup {parent[n]})

Ancestors(n) == AncestorsAcc(n, {})

(* At termination, parent pointers form a tree rooted at the initiator:  *)
(* every non-initiator node has the initiator as an ancestor, no node is *)
(* its own ancestor, and every node other than the initiator has a parent. *)
AncestorProp ==
    (\A n \in Node : pc[n] = "Done") =>
        /\ \A n \in Node \ {initiator} :
              /\ parent[n] # NoNode
              /\ initiator \in Ancestors(n)
        /\ \A n \in Node : n \notin Ancestors(n)

=============================================================================