----------------------------- MODULE Echo -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,       \* set of nodes
          initiator,  \* single initiator, root of the spanning tree
          R           \* neighborhood relation, a Boolean function over Node \X Node

(***************************************************************************)
(* Properties of binary relations represented as Boolean functions.        *)
(***************************************************************************)
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

ReachableFrom(rel, S, x) ==
  LET f[k \in 0..Cardinality(S)] ==
        IF k = 0 THEN {x}
        ELSE f[k-1] \cup { z \in S : \E y \in f[k-1] : rel[y, z] }
  IN  f[Cardinality(S)]

IsConnected(rel, S) == \A x, y \in S : y \in ReachableFrom(rel, S, x)

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];
    define {
       send(box, dest, msg) == [box EXCEPT ![dest] = @ \cup {msg}]
       multicast(box, dests, msg) ==
          [n \in Node |-> IF n \in dests THEN box[n] \cup {msg} ELSE box[n]]
    }
    process (node \in Node)
      variables parent = NoNode,
                children = {},
                rcvd = 0,
                nbrs = neighbors(self);
    {
      n0: if (self = initiator) {
             inbox := multicast(inbox, nbrs, [kind |-> "m", sndr |-> self])
          };
      n1: while (rcvd < Cardinality(nbrs)) {
             with (msg \in inbox[self]) {
                if (msg.kind = "m" /\ self # initiator /\ rcvd = 0) {
                   parent := msg.sndr;
                   inbox := [n \in Node |->
                               IF n = self THEN inbox[self] \ {msg}
                               ELSE IF n \in nbrs \ {msg.sndr}
                                    THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                    ELSE inbox[n]]
                } else {
                   if (msg.kind = "c") { children := children \cup {msg.sndr} };
                   inbox[self] := inbox[self] \ {msg}
                };
                rcvd := rcvd + 1
             }
          };
      n2: if (self # initiator) {
             inbox := send(inbox, parent, [kind |-> "c", sndr |-> self])
          }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inbox, pc

(* define statement *)
send(box, dest, msg) == [box EXCEPT ![dest] = @ \cup {msg}]
multicast(box, dests, msg) ==
   [n \in Node |-> IF n \in dests THEN box[n] \cup {msg} ELSE box[n]]

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
                  THEN /\ inbox' = multicast(inbox, nbrs[self], [kind |-> "m", sndr |-> self])
                  ELSE /\ TRUE
                       /\ UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            /\ IF msg.kind = "m" /\ self # initiator /\ rcvd[self] = 0
                                  THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                       /\ inbox' = [n \in Node |->
                                                      IF n = self THEN inbox[self] \ {msg}
                                                      ELSE IF n \in nbrs[self] \ {msg.sndr}
                                                           THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                                           ELSE inbox[n]]
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
                  THEN /\ inbox' = send(inbox, parent[self], [kind |-> "c", sndr |-> self])
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
(* Correctness properties                                                  *)
(***************************************************************************)
Message == [kind : {"m", "c"}, sndr : Node]

TypeOK ==
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ inbox \in [Node -> SUBSET Message]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])

InitiatorNoParent == parent[initiator] = NoNode

ParentIsNeighbor == \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

ParentChild == \A m, n \in Node : n \in children[m] => parent[n] = m

\* set of (strict) ancestors of a node in the parent relation
Ancestors(n) ==
  LET f[k \in 0..Cardinality(Node)] ==
        IF k = 0
        THEN (IF parent[n] = NoNode THEN {} ELSE {parent[n]})
        ELSE f[k-1] \cup { parent[x] : x \in { y \in f[k-1] : parent[y] # NoNode } }
  IN  f[Cardinality(Node)]

AncestorProperties ==
  (\A n \in Node : pc[n] = "Done") =>
     \A n \in Node \ {initiator} :
        /\ parent[n] \in Node
        /\ initiator \in Ancestors(n)
        /\ n \notin Ancestors(n)

=============================================================================