------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R

(***************************************************************************)
(* Transitive closure of a binary relation over a finite set S,            *)
(* represented as a Boolean-valued function on S \X S.                     *)
(***************************************************************************)
TransitiveClosure(Rel, S) ==
  LET f[k \in 0..Cardinality(S)] ==
        IF k = 0 THEN Rel
        ELSE [p \in S \X S |->
                \/ f[k-1][p]
                \/ \E z \in S : f[k-1][p[1], z] /\ Rel[z, p[2]]]
  IN  f[Cardinality(S)]

IsIrreflexive(Rel, S) == \A s \in S : ~ Rel[s, s]
IsSymmetric(Rel, S) == \A s, t \in S : Rel[s, t] <=> Rel[t, s]
IsConnected(Rel, S) ==
  LET tc == TransitiveClosure(Rel, S)
  IN  \A s, t \in S : s # t => tc[s, t]

ASSUME
  /\ initiator \in Node
  /\ R \in [Node \X Node -> BOOLEAN]
  /\ IsIrreflexive(R, Node)
  /\ IsSymmetric(R, Node)
  /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

Msg == [kind : {"m", "c"}, sndr : Node]

VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ pc = [n \in Node |-> "n0"]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ nbrs = [n \in Node |-> neighbors(n)]

(* multicast a message of the given kind from self to all nodes in dests *)
Multicast(ib, self, dests, kind) ==
  [n \in Node |-> IF n \in dests
                    THEN ib[n] \cup {[kind |-> kind, sndr |-> self]}
                    ELSE ib[n]]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN /\ inbox' = Multicast(inbox, self, nbrs[self], "m")
            /\ pc' = [pc EXCEPT ![self] = "n2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED inbox
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ \E msg \in inbox[self] :
       LET ib1 == [inbox EXCEPT ![self] = inbox[self] \ {msg}]
           newNbrs == nbrs[self] \ {msg.sndr}
       IN  /\ parent' = [parent EXCEPT ![self] = msg.sndr]
           /\ rcvd' = [rcvd EXCEPT ![self] = 1]
           /\ nbrs' = [nbrs EXCEPT ![self] = newNbrs]
           /\ inbox' = Multicast(ib1, self, newNbrs, "m")
  /\ pc' = [pc EXCEPT ![self] = "n2"]
  /\ UNCHANGED children

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF rcvd[self] < Cardinality(neighbors(self))
       THEN /\ \E msg \in inbox[self] :
                 /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                 /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                 /\ children' = IF msg.kind = "c"
                                  THEN [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                  ELSE children
            /\ pc' = [pc EXCEPT ![self] = "n2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "n3"]
            /\ UNCHANGED << inbox, rcvd, children >>
  /\ UNCHANGED << parent, nbrs >>

n3(self) ==
  /\ pc[self] = "n3"
  /\ IF self # initiator
       THEN inbox' = [inbox EXCEPT ![parent[self]] =
                         inbox[parent[self]] \cup {[kind |-> "c", sndr |-> self]}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self) \/ n3(self)

Terminating ==
  /\ \A self \in Node : pc[self] = "Done"
  /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in Node : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
  /\ pc \in [Node -> {"n0", "n1", "n2", "n3", "Done"}]
  /\ parent \in [Node -> (Node \cup {NoNode})]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : /\ nbrs[n] \subseteq neighbors(n)
                     /\ rcvd[n] <= Cardinality(neighbors(n))

InitiatorNoParent == parent[initiator] = NoNode

ParentIsNeighbor ==
  \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

ParentChild ==
  \A m, n \in Node : n \in children[m] => /\ m = parent[n]
                                          /\ m \in neighbors(n)

ParentRel == [p \in Node \X Node |-> parent[p[1]] = p[2]]

AncestorProperties ==
  (\A n \in Node : pc[n] = "Done") =>
    LET anc == TransitiveClosure(ParentRel, Node)
    IN  /\ \A n \in Node \ {initiator} : anc[n, initiator]
        /\ \A n \in Node : ~ anc[n, n]

=============================================================================