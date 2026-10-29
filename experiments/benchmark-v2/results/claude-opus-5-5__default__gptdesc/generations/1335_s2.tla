-------------------------------- MODULE Echo --------------------------------
(***************************************************************************)
(* The Echo algorithm for constructing a spanning tree in an undirected    *)
(* graph, starting from a single initiator node. The algorithm was written *)
(* as a PlusCal algorithm (shown in the comment below) and translated into *)
(* TLA+ with explicit state variables and actions.                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node,        \* set of nodes of the graph
          initiator,   \* the single initiator node
          R            \* neighborhood relation, R[m,n] = TRUE iff m and n are adjacent

(***************************************************************************)
(* Operators on binary relations, represented as sets of pairs.            *)
(***************************************************************************)
Compose(A, B) == { <<pq[1][1], pq[2][2]>> : pq \in { x \in A \X B : x[1][2] = x[2][1] } }

RECURSIVE Iter(_, _)
Iter(Rel, k) == IF k = 0 THEN Rel
                ELSE LET P == Iter(Rel, k-1) IN P \cup Compose(P, Rel)

\* Transitive closure of a relation over the (finite) set of nodes
TC(Rel) == Iter(Rel, Cardinality(Node))

Edges == { e \in Node \X Node : R[e[1], e[2]] }

IsIrreflexive == \A n \in Node : ~ R[n, n]
IsSymmetric   == \A m, n \in Node : R[m, n] = R[n, m]
IsConnected   == \A m, n \in Node : m # n => <<m, n>> \in TC(Edges)

ASSUME
  /\ IsFiniteSet(Node)
  /\ initiator \in Node
  /\ R \in [Node \X Node -> BOOLEAN]
  /\ IsIrreflexive
  /\ IsSymmetric
  /\ IsConnected

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

Message == [kind : {"m1", "m2"}, sndr : Node]

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];
    process (node \in Node)
      variables parent = NoNode, children = {}, rcvd = 0,
                nbrs = neighbors(self);
    {
    n0: if (self = initiator) {
          \* initiator sends an explore message (m1) to all its neighbors
          inbox := [n \in Node |-> IF n \in nbrs
                                   THEN inbox[n] \cup {[kind |-> "m1", sndr |-> self]}
                                   ELSE inbox[n]];
        };
    n1: while (rcvd < Cardinality(nbrs)) {
          with (msg \in inbox[self]) {
            if (self # initiator /\ rcvd = 0) {
              \* first message: adopt sender as parent, forward to other neighbors
              parent := msg.sndr;
              inbox := [n \in Node |->
                          IF n = self THEN inbox[self] \ {msg}
                          ELSE IF n \in nbrs \ {msg.sndr}
                               THEN inbox[n] \cup {[kind |-> "m1", sndr |-> self]}
                               ELSE inbox[n]];
            } else {
              if (msg.kind = "m2") { children := children \cup {msg.sndr} };
              inbox[self] := inbox[self] \ {msg};
            };
            rcvd := rcvd + 1;
          }
        };
    n2: if (self # initiator) {
          \* echo (m2) to the parent
          inbox[parent] := inbox[parent] \cup {[kind |-> "m2", sndr |-> self]};
        };
    }
}
***************************************************************************)

VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == Node

Init == /\ inbox = [n \in Node |-> {}]
        /\ parent = [self \in Node |-> NoNode]
        /\ children = [self \in Node |-> {}]
        /\ rcvd = [self \in Node |-> 0]
        /\ nbrs = [self \in Node |-> neighbors(self)]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF self = initiator
                  THEN inbox' = [n \in Node |->
                                   IF n \in nbrs[self]
                                   THEN inbox[n] \cup {[kind |-> "m1", sndr |-> self]}
                                   ELSE inbox[n]]
                  ELSE UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self] :
                            /\ IF self # initiator /\ rcvd[self] = 0
                                  THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                       /\ inbox' = [n \in Node |->
                                                      IF n = self THEN inbox[self] \ {msg}
                                                      ELSE IF n \in nbrs[self] \ {msg.sndr}
                                                           THEN inbox[n] \cup {[kind |-> "m1", sndr |-> self]}
                                                           ELSE inbox[n]]
                                       /\ UNCHANGED children
                                  ELSE /\ children' = IF msg.kind = "m2"
                                                         THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                                                         ELSE children
                                       /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                                       /\ UNCHANGED parent
                            /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN inbox' = [inbox EXCEPT ![parent[self]] =
                                    @ \cup {[kind |-> "m2", sndr |-> self]}]
                  ELSE UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
TypeOK ==
  /\ inbox \in [Node -> SUBSET Message]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])

\* the initiator never gets a parent
InitiatorNoParent == parent[initiator] = NoNode

\* parents are always neighbors
ParentIsNeighbor == \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

\* every child of a node has that node as its parent
ParentChild == \A n \in Node : \A c \in children[n] :
                  /\ parent[c] = n
                  /\ c \in neighbors(n)

ParentRel == { <<n, parent[n]>> : n \in { m \in Node : parent[m] \in Node } }

\* the parent relation never contains a cycle
Acyclic == \A n \in Node : <<n, n>> \notin TC(ParentRel)

\* upon termination the parent relation is a spanning tree rooted at the initiator
Finished == \A n \in Node : pc[n] = "Done"

SpanningTree ==
  Finished =>
    /\ \A n \in Node \ {initiator} :
          /\ parent[n] \in neighbors(n)
          /\ n \in children[parent[n]]
          /\ <<n, initiator>> \in TC(ParentRel)
    /\ \A n \in Node : inbox[n] = {}

Invariants == TypeOK /\ InitiatorNoParent /\ ParentIsNeighbor
              /\ ParentChild /\ Acyclic /\ SpanningTree

\* every node eventually finishes
Termination == <>Finished

THEOREM Spec => []Invariants
THEOREM Spec => Termination
=============================================================================