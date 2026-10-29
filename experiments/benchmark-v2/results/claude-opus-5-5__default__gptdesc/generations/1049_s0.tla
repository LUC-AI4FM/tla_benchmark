------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, will be the root of the tree
          R          \* neighborhood relation, a Boolean function over Node \X Node

-----------------------------------------------------------------------------
(* Graph-theoretic helper operators                                         *)

IsIrreflexive(rel, S) == \A m \in S : ~ rel[m, m]

IsSymmetric(rel, S) == \A m, n \in S : rel[m, n] = rel[n, m]

RECURSIVE ReachSet(_, _, _, _)
ReachSet(rel, S, X, k) ==
    IF k = 0 THEN X
    ELSE ReachSet(rel, S, X \cup {m \in S : \E x \in X : rel[x, m]}, k - 1)

IsConnected(rel, S) ==
    \A m \in S : ReachSet(rel, S, {m}, Cardinality(S)) = S

ASSUME /\ initiator \in Node
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
        multicast(box, snd, rcvs, msg) ==
            [m \in Node |-> IF m \in rcvs THEN box[m] \cup {msg} ELSE box[m]]
    }
    fair process (node \in Node)
      variables parent = NoNode,
                children = {},
                rcvd = 0,
                nbrs = neighbors(self);
    {
      n0: if (self = initiator) {
             inbox := multicast(inbox, self, nbrs, [kind |-> "m", sndr |-> self])
          };
      n1: while (rcvd < Cardinality(nbrs)) {
             with (msg \in inbox[self],
                   net = [inbox EXCEPT ![self] = @ \ {msg}]) {
                rcvd := rcvd + 1;
                if (self # initiator /\ rcvd = 1) {
                   assert(msg.kind = "m");
                   parent := msg.sndr;
                   inbox := multicast(net, self, nbrs \ {msg.sndr},
                                      [kind |-> "m", sndr |-> self])
                } else {
                   if (msg.kind = "c") {
                      children := children \cup {msg.sndr}
                   };
                   inbox := net
                }
             }
          };
      n2: if (self # initiator) {
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
multicast(box, snd, rcvs, msg) ==
    [m \in Node |-> IF m \in rcvs THEN box[m] \cup {msg} ELSE box[m]]

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
                       /\ inbox' = inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            LET net == [inbox EXCEPT ![self] = @ \ {msg}] IN
                              /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                              /\ IF self # initiator /\ rcvd'[self] = 1
                                    THEN /\ Assert(msg.kind = "m",
                                                   "Failure of assertion at line 1, column 1.")
                                         /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                         /\ inbox' = multicast(net, self, nbrs[self] \ {msg.sndr},
                                                               [kind |-> "m", sndr |-> self])
                                         /\ UNCHANGED children
                                    ELSE /\ IF msg.kind = "c"
                                               THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED children
                                         /\ inbox' = net
                                         /\ UNCHANGED parent
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ Assert(parent[self] \in nbrs[self],
                                 "Failure of assertion at line 1, column 1.")
                       /\ inbox' = send(inbox, self, parent[self],
                                        [kind |-> "c", sndr |-> self])
                  ELSE /\ TRUE
                       /\ inbox' = inbox
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
-----------------------------------------------------------------------------
(* Correctness properties                                                   *)

TypeOK ==
    /\ inbox \in [Node -> SUBSET Message]
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]
    /\ \A n \in Node :
          /\ nbrs[n] = neighbors(n)
          /\ rcvd[n] <= Cardinality(nbrs[n])
          /\ \A msg \in inbox[n] : msg.sndr \in nbrs[n]

\* The initiator never has a parent.
InitiatorNoParent == parent[initiator] = NoNode

\* The parent of every node (if any) is a neighbor of that node.
ParentIsNeighbor ==
    \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

\* Every child of a node m has m as its parent.
ParentChild ==
    \A m, n \in Node : n \in children[m] => /\ m = parent[n]
                                            /\ m \in neighbors(n)

\* Iterated application of the parent function.
RECURSIVE ParentIter(_, _)
ParentIter(n, k) ==
    IF k = 0 \/ n = NoNode THEN n
    ELSE ParentIter(parent[n], k - 1)

IsAncestor(a, n) == \E k \in 1..Cardinality(Node) : ParentIter(n, k) = a

AllDone == \A n \in Node : pc[n] = "Done"

\* At termination, the parent relation forms a spanning tree rooted at the initiator.
AncestorProp ==
    AllDone =>
      /\ \A n \in Node \ {initiator} : IsAncestor(initiator, n)
      /\ \A n \in Node : ~ IsAncestor(n, n)
      /\ \A m, n \in Node : (n # initiator /\ parent[n] = m) <=> n \in children[m]

THEOREM Spec => []TypeOK
THEOREM Spec => []InitiatorNoParent
THEOREM Spec => []ParentIsNeighbor
THEOREM Spec => []ParentChild
THEOREM Spec => []AncestorProp
THEOREM Spec => Termination
=============================================================================