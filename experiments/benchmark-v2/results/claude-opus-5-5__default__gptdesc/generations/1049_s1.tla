-------------------------------- MODULE Echo --------------------------------
(***************************************************************************)
(* The Echo algorithm builds a spanning tree of an undirected, connected   *)
(* graph, starting from a single initiator node.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, will be the root of the tree
          R          \* neighborhood relation, a Boolean function over nodes

(***************************************************************************)
(* Graph-theoretic helper definitions                                      *)
(***************************************************************************)
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

\* Set of nodes reachable from node n via the relation rel.
ReachableFrom(rel, S, n) ==
    LET Step(T) == T \cup {y \in S : \E x \in T : rel[x, y]}
        RECURSIVE Fix(_)
        Fix(T) == IF Step(T) = T THEN T ELSE Fix(Step(T))
    IN  Fix({n})

IsConnected(rel, S) == \A m \in S : ReachableFrom(rel, S, m) = S

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

Message == [kind : {"m", "c"}, sndr : Node]

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];
    define {
        \* send msg from node s to node t
        send(box, s, t, msg) == [box EXCEPT ![t] = @ \cup {msg}]
        \* send msg from s to all neighbors of s except excl
        multicast(box, s, excl, msg) ==
            [m \in Node |-> IF R[s, m] /\ m # excl
                              THEN box[m] \cup {msg}
                              ELSE box[m]]
    }
    fair process (node \in Node)
      variables parent = NoNode,
                children = {},
                rcvd = 0,
                nbrs = neighbors(self); {
n0: if (self = initiator) {
       inbox := multicast(inbox, self, NoNode, [kind |-> "m", sndr |-> self]);
    };
n1: while (rcvd < Cardinality(nbrs)) {
       with (msg \in inbox[self]) {
          if (msg.kind = "m" /\ rcvd = 0 /\ self # initiator) {
             parent := msg.sndr;
             inbox := multicast([inbox EXCEPT ![self] = @ \ {msg}],
                                self, msg.sndr, [kind |-> "m", sndr |-> self]);
          } else if (msg.kind = "c") {
             children := children \cup {msg.sndr};
             inbox := [inbox EXCEPT ![self] = @ \ {msg}];
          } else {
             inbox := [inbox EXCEPT ![self] = @ \ {msg}];
          };
       };
       rcvd := rcvd + 1;
    };
n2: if (self # initiator) {
       inbox := send(inbox, self, parent, [kind |-> "c", sndr |-> self]);
    };
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inbox, pc

(* define statement *)
send(box, s, t, msg) == [box EXCEPT ![t] = @ \cup {msg}]

multicast(box, s, excl, msg) ==
    [m \in Node |-> IF R[s, m] /\ m # excl
                      THEN box[m] \cup {msg}
                      ELSE box[m]]

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
                  THEN /\ inbox' = multicast(inbox, self, NoNode,
                                             [kind |-> "m", sndr |-> self])
                  ELSE /\ TRUE
                       /\ inbox' = inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            IF msg.kind = "m" /\ rcvd[self] = 0 /\ self # initiator
                               THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                    /\ inbox' = multicast([inbox EXCEPT ![self] = @ \ {msg}],
                                                          self, msg.sndr,
                                                          [kind |-> "m", sndr |-> self])
                                    /\ UNCHANGED children
                               ELSE /\ IF msg.kind = "c"
                                          THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                               /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                                          ELSE /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                                               /\ UNCHANGED children
                                    /\ UNCHANGED parent
                       /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ inbox' = send(inbox, self, parent[self],
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

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
TypeOK ==
    /\ inbox \in [Node -> SUBSET Message]
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]
    /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])

\* The initiator never has a parent.
InitiatorNoParent == parent[initiator] = NoNode

\* A node's parent, if any, is one of its neighbors.
ParentNeighbor == \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

\* If n is a child of m, then m is the parent of n.
ParentChild ==
    /\ \A m, n \in Node : n \in children[m] => m = parent[n]
    \* At termination, the converse also holds.
    /\ (\A n \in Node : pc[n] = "Done") =>
           \A m, n \in Node : parent[n] = m => n \in children[m]

\* Set of ancestors of node n following the parent pointers.
Ancestors(n) ==
    LET Step(T) == T \cup ({parent[x] : x \in T} \ {NoNode})
        RECURSIVE Fix(_)
        Fix(T) == IF Step(T) = T THEN T ELSE Fix(Step(T))
    IN  Fix({n}) \ {n}

\* At termination, every non-initiator node has a parent, and the
\* initiator is an ancestor of every other node (no cycles).
AncestorProp ==
    (\A n \in Node : pc[n] = "Done") =>
        \A n \in Node \ {initiator} :
            /\ parent[n] \in Node
            /\ initiator \in Ancestors(n)
            /\ n \notin Ancestors(n)

\* All processes eventually terminate.
THEOREM Spec => []TypeOK
THEOREM Spec => [](InitiatorNoParent /\ ParentNeighbor /\ ParentChild /\ AncestorProp)
THEOREM Spec => Termination

=============================================================================