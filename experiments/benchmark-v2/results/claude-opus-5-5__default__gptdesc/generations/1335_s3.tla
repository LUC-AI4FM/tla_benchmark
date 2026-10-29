---------------------------- MODULE Echo ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,       \* set of nodes
          initiator,  \* single initiator, the root of the spanning tree
          R           \* neighborhood relation, a Boolean function over Node \X Node

(***************************************************************************)
(* Auxiliary graph-theoretic definitions                                   *)
(***************************************************************************)
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

\* Nodes reachable from initiator in at most k steps
ReachFromInit[k \in Nat] ==
    IF k = 0 THEN {initiator}
    ELSE ReachFromInit[k-1] \cup
           { m \in Node : \E n \in ReachFromInit[k-1] : R[n, m] }

\* For a symmetric relation, connectedness amounts to every node being
\* reachable from the initiator.
IsConnected(rel, S) == ReachFromInit[Cardinality(S)] = S

ASSUME /\ IsFiniteSet(Node)
       /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

Message == [kind : {"m", "c"}, sndr : Node]

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];
    define {
        send(box, i, j, msg) == [box EXCEPT ![j] = @ \cup {msg}]
        multicast(box, i, recipients, msg) ==
            [m \in Node |-> IF m \in recipients THEN box[m] \cup {msg}
                                               ELSE box[m]]
    }
    fair process (node \in Node)
      variables parent = NoNode, children = {},
                rcvd = 0, nbrs = neighbors(self);
    {
    n0: if (self = initiator) {
           inbox := multicast(inbox, self, nbrs, [kind |-> "m", sndr |-> self]);
        };
    n1: while (rcvd < Cardinality(nbrs)) {
          with (msg \in inbox[self]) {
             rcvd := rcvd + 1;
             if (self # initiator /\ rcvd = 1) {
                assert(msg.kind = "m");
                parent := msg.sndr;
                inbox := [multicast(inbox, self, nbrs \ {msg.sndr},
                                    [kind |-> "m", sndr |-> self])
                          EXCEPT ![self] = @ \ {msg}];
             } else {
                if (msg.kind = "c") { children := children \cup {msg.sndr} };
                inbox[self] := inbox[self] \ {msg};
             }
          }
        };
    n2: if (self # initiator) {
          assert(parent \in nbrs);
          inbox := send(inbox, self, parent, [kind |-> "c", sndr |-> self]);
        }
    }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES inbox, pc

(* define statement *)
send(box, i, j, msg) == [box EXCEPT ![j] = @ \cup {msg}]

multicast(box, i, recipients, msg) ==
    [m \in Node |-> IF m \in recipients THEN box[m] \cup {msg} ELSE box[m]]

VARIABLES parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == Node

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
                  THEN inbox' = multicast(inbox, self, nbrs[self],
                                          [kind |-> "m", sndr |-> self])
                  ELSE UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                            /\ IF self # initiator /\ rcvd'[self] = 1
                                  THEN /\ Assert(msg.kind = "m",
                                                 "Failure of assertion at line 46, column 17.")
                                       /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                       /\ inbox' = [multicast(inbox, self,
                                                      nbrs[self] \ {msg.sndr},
                                                      [kind |-> "m", sndr |-> self])
                                                    EXCEPT ![self] = @ \ {msg}]
                                       /\ UNCHANGED children
                                  ELSE /\ IF msg.kind = "c"
                                             THEN children' = [children EXCEPT
                                                     ![self] = children[self] \cup {msg.sndr}]
                                             ELSE UNCHANGED children
                                       /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                                       /\ UNCHANGED parent
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ Assert(parent[self] \in nbrs[self],
                                 "Failure of assertion at line 61, column 11.")
                       /\ inbox' = send(inbox, self, parent[self],
                                        [kind |-> "c", sndr |-> self])
                  ELSE UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

\* END TRANSLATION

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]
    /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])
    /\ inbox \in [Node -> SUBSET Message]
    /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in nbrs[n]
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]

\* The initiator never acquires a parent; every other node that has
\* received a message has a neighbor as its parent.
ParentNeighbor ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node \ {initiator} :
          rcvd[n] > 0 => parent[n] \in nbrs[n]

\* Children are always nodes whose parent is the node, and once a node
\* has finished, all nodes having it as parent are among its children.
ParentChild ==
    \A m, n \in Node :
        /\ n \in children[m] => m = parent[n]
        /\ (m = parent[n] /\ pc[m] = "Done") => n \in children[m]

\* Following parent pointers k times (stopping at initiator or NoNode)
ParentIter[k \in Nat] ==
    IF k = 0 THEN [n \in Node |-> n]
    ELSE [n \in Node |->
            LET p == ParentIter[k-1][n]
            IN  IF p = initiator \/ p = NoNode THEN p ELSE parent[p]]

\* Upon termination, the parent relation forms a spanning tree rooted at
\* the initiator: every node reaches the initiator via parent pointers
\* (hence the relation is acyclic and contains all nodes).
SpanningTree ==
    (\A n \in Node : pc[n] = "Done") =>
        \A n \in Node : ParentIter[Cardinality(Node)][n] = initiator

\* Parent pointers never form a cycle.
Acyclic ==
    \A n \in Node : ParentIter[Cardinality(Node)][n] \in {initiator, NoNode}

\* Upon termination, no messages remain in transit.
NoMessagesAtEnd ==
    (\A n \in Node : pc[n] = "Done") => \A n \in Node : inbox[n] = {}

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>(\A n \in Node : pc[n] = "Done")

THEOREM Spec => [](TypeOK /\ ParentNeighbor /\ ParentChild /\ SpanningTree
                   /\ Acyclic /\ NoMessagesAtEnd)
THEOREM Spec => Termination
=============================================================================