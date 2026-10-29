------------------------------- MODULE Echo -------------------------------
(***************************************************************************)
(* The Echo algorithm builds a spanning tree in an undirected, connected   *)
(* graph, starting from a designated initiator node that becomes the root. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Operators on binary relations, represented as Boolean-valued functions  *)
(* over S \X S.                                                            *)
(***************************************************************************)
IsIrreflexive(Rel, S) == \A s \in S : ~ Rel[s, s]

IsSymmetric(Rel, S) == \A s, t \in S : Rel[s, t] <=> Rel[t, s]

TransitiveClosure(Rel, S) ==
  LET f[k \in Nat] ==
        IF k = 0 THEN Rel
        ELSE [p \in S \X S |->
                \/ f[k-1][p]
                \/ \E z \in S : f[k-1][p[1], z] /\ Rel[z, p[2]]]
  IN  f[Cardinality(S)]

IsConnected(Rel, S) ==
  LET tc == TransitiveClosure(Rel, S)
  IN  \A s, t \in S : s = t \/ tc[s, t]

CONSTANTS Node, initiator, R

ASSUME
  /\ initiator \in Node
  /\ R \in [Node \X Node -> BOOLEAN]
  /\ IsIrreflexive(R, Node)
  /\ IsSymmetric(R, Node)
  /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

Message == [kind : {"m", "c"}, sndr : Node]

multicast(inb, p, nbs, msg) ==
  [n \in Node |-> IF n \in nbs
                    THEN inb[n] \cup {[kind |-> msg, sndr |-> p]}
                    ELSE inb[n]]

VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == <<inbox, pc, parent, children, rcvd, nbrs>>

ProcSet == Node

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ parent = [self \in Node |-> NoNode]
  /\ children = [self \in Node |-> {}]
  /\ rcvd = [self \in Node |-> 0]
  /\ nbrs = [self \in Node |-> neighbors(self)]
  /\ pc = [self \in ProcSet |-> "n0"]

(* The initiator multicasts "m" to all its neighbors. *)
n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN inbox' = multicast(inbox, self, nbrs[self], "m")
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

(* Receive messages until one has been received from every neighbor. *)
n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(neighbors(self))
       THEN /\ \E msg \in inbox[self] :
                 /\ IF rcvd[self] = 0 /\ self # initiator
                      THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                           /\ nbrs' = [nbrs EXCEPT ![self] = nbrs[self] \ {msg.sndr}]
                           /\ inbox' = multicast([inbox EXCEPT ![self] = inbox[self] \ {msg}],
                                                 self, nbrs[self] \ {msg.sndr}, "m")
                      ELSE /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                           /\ UNCHANGED <<parent, nbrs>>
                 /\ children' = IF msg.kind = "c"
                                  THEN [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                  ELSE children
                 /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "n1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED <<inbox, parent, children, rcvd, nbrs>>

(* A non-initiator sends a "c" message to its parent. *)
n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
       THEN inbox' = [inbox EXCEPT ![parent[self]] =
                        inbox[parent[self]] \cup {[kind |-> "c", sndr |-> self]}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
  /\ inbox \in [Node -> SUBSET Message]
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] \subseteq neighbors(n)

InitiatorNoParent == parent[initiator] = NoNode

ParentIsNeighbor ==
  \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

ParentChild ==
  \A m, n \in Node : n \in children[m] => m = parent[n]

ParentRel == [p \in Node \X Node |-> parent[p[1]] = p[2]]

Ancestor == TransitiveClosure(ParentRel, Node)

AncestorProp ==
  (\A n \in Node : pc[n] = "Done") =>
     LET anc == Ancestor
     IN  /\ \A n \in Node \ {initiator} : anc[n, initiator]
         /\ IsIrreflexive(anc, Node)

=============================================================================