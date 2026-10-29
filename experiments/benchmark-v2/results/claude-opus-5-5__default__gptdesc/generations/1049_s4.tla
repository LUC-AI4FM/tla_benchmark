--------------------------------- MODULE Echo ---------------------------------
(***************************************************************************)
(* The Echo algorithm for constructing a spanning tree in an undirected,   *)
(* connected graph, starting from a single initiator.                      *)
(*                                                                         *)
(* The graph is a set of nodes Node with a Boolean neighborhood relation   *)
(* R, which is assumed to be irreflexive, symmetric and connected.         *)
(* Communication uses per-node inboxes that hold sets of message records.  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R

(***************************************************************************)
(* Operators on relations, represented as Boolean functions on S \X S.     *)
(***************************************************************************)
IsIrreflexive(Rel, S) == \A s \in S : ~ Rel[s, s]

IsSymmetric(Rel, S) == \A s, t \in S : Rel[s, t] <=> Rel[t, s]

\* The set of elements of S reachable from x by zero or more Rel-steps.
ReachableFrom(Rel, S, x) ==
  LET f[k \in 0 .. Cardinality(S)] ==
        IF k = 0 THEN {x}
        ELSE f[k-1] \cup {y \in S : \E z \in f[k-1] : Rel[z, y]}
  IN  f[Cardinality(S)]

IsConnected(Rel, S) == \A m, n \in S : n \in ReachableFrom(Rel, S, m)

ASSUME EchoAssumptions ==
  /\ IsFiniteSet(Node)
  /\ initiator \in Node
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
      \* send message msg to all nodes in set dests
      multicast(box, dests, msg) ==
         [n \in Node |-> IF n \in dests THEN box[n] \cup {msg} ELSE box[n]]
    }
    process (node \in Node)
      variables parent = NoNode, children = {}, rcvd = 0,
                nbrs = neighbors(self);
    {
    n0: if (self = initiator) {
           \* initiator sends first message to all neighbors
           inbox := multicast(inbox, nbrs, [kind |-> "m", sndr |-> self])
        };
    n1: while (rcvd < Cardinality(nbrs)) {
          \* receive some message
          with (msg \in inbox[self]) {
            if (msg.kind = "m" /\ self # initiator /\ rcvd = 0) {
               \* first explorer message: sender becomes parent,
               \* forward explorer to all neighbors except the parent
               parent := msg.sndr;
               inbox := [multicast(inbox, nbrs \ {msg.sndr},
                                   [kind |-> "m", sndr |-> self])
                         EXCEPT ![self] = inbox[self] \ {msg}]
            } else {
               if (msg.kind = "c") {
                  children := children \cup {msg.sndr}
               };
               inbox[self] := inbox[self] \ {msg}
            }
          };
          rcvd := rcvd + 1
        };
    n2: if (self # initiator) {
          \* echo back to the parent
          inbox[parent] := inbox[parent] \cup {[kind |-> "c", sndr |-> self]}
        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inbox, pc

(* define statement *)
multicast(box, dests, msg) ==
   [n \in Node |-> IF n \in dests THEN box[n] \cup {msg} ELSE box[n]]

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
                  THEN /\ inbox' = multicast(inbox, nbrs[self],
                                             [kind |-> "m", sndr |-> self])
                  ELSE /\ TRUE
                       /\ inbox' = inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            IF msg.kind = "m" /\ self # initiator /\ rcvd[self] = 0
                               THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                    /\ inbox' = [multicast(inbox, nbrs[self] \ {msg.sndr},
                                                           [kind |-> "m", sndr |-> self])
                                                 EXCEPT ![self] = inbox[self] \ {msg}]
                                    /\ UNCHANGED children
                               ELSE /\ IF msg.kind = "c"
                                          THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED children
                                    /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                                    /\ UNCHANGED parent
                       /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ inbox' = [inbox EXCEPT ![parent[self]] =
                                      inbox[parent[self]] \cup {[kind |-> "c", sndr |-> self]}]
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

-------------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
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

\* The parent of a node (if any) is one of its neighbors.
ParentIsNeighbor ==
  \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

\* Children of a node have that node as their parent.
ParentChild ==
  \A m, n \in Node : n \in children[m] => m = parent[n]

\* The parent relation as a Boolean relation: ParentRel[m,n] iff m is n's parent.
ParentRel == [x \in Node \X Node |-> parent[x[2]] = x[1]]

AllDone == \A n \in Node : pc[n] = "Done"

\* At termination, every non-initiator node has a parent, the children sets
\* coincide with the inverse parent relation, and the initiator is an
\* ancestor of every node, i.e. the parent relation forms a spanning tree.
AncestorProp ==
  AllDone =>
    /\ \A n \in Node \ {initiator} : parent[n] \in neighbors(n)
    /\ \A m, n \in Node : n \in children[m] <=> m = parent[n]
    /\ \A n \in Node : n \in ReachableFrom(ParentRel, Node, initiator)

Invariants ==
  /\ TypeOK
  /\ InitiatorNoParent
  /\ ParentIsNeighbor
  /\ ParentChild
  /\ AncestorProp

THEOREM Spec => []Invariants
THEOREM Spec => Termination
===============================================================================