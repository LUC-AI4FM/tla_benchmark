------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, root of the spanning tree
          R          \* neighborhood relation, Boolean function over Node \X Node

-----------------------------------------------------------------------------
(* Relation helpers *)

RelAsSet(rel, S) == { e \in S \X S : rel[e[1], e[2]] }

TransClosure(E, S) ==
  LET f[k \in 0..(Cardinality(S) + 1)] ==
        IF k = 0 THEN E
        ELSE f[k-1] \cup
               { e \in S \X S :
                   \E b \in S : <<e[1], b>> \in f[k-1] /\ <<b, e[2]>> \in f[k-1] }
  IN f[Cardinality(S) + 1]

IsIrreflexive(rel, S) == \A a \in S : ~ rel[a, a]

IsSymmetric(rel, S) == \A a, b \in S : rel[a, b] => rel[b, a]

IsConnected(rel, S) ==
  LET tc == TransClosure(RelAsSet(rel, S), S)
  IN  \A a, b \in S : a = b \/ <<a, b>> \in tc

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x \in {"NoNode", "none", "nil"} : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

Msg == [kind : {"m", "c"}, sndr : Node]

-----------------------------------------------------------------------------
VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ pc = [n \in Node |-> "n0"]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ nbrs = [n \in Node |-> neighbors(n)]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN /\ inbox' = [n \in Node |->
                           IF n \in nbrs[self]
                             THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                             ELSE inbox[n]]
            /\ UNCHANGED << parent, rcvd, nbrs >>
       ELSE \E msg \in inbox[self] :
              LET newNbrs == nbrs[self] \ {msg.sndr}
              IN  /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                  /\ rcvd' = [rcvd EXCEPT ![self] = 1]
                  /\ nbrs' = [nbrs EXCEPT ![self] = newNbrs]
                  /\ inbox' = [n \in Node |->
                                 IF n = self
                                   THEN inbox[n] \ {msg}
                                 ELSE IF n \in newNbrs
                                   THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                 ELSE inbox[n]]
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED children

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(neighbors(self))
       THEN \E msg \in inbox[self] :
              /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
              /\ children' = IF msg.kind = "c"
                               THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                               ELSE children
              /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
              /\ pc' = pc
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED << rcvd, children, inbox >>
  /\ UNCHANGED << parent, nbrs >>

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF parent[self] # NoNode
       THEN inbox' = [inbox EXCEPT ![parent[self]] =
                        @ \cup {[kind |-> "c", sndr |-> self]}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A self \in Node : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in Node : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Correctness properties *)

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]

ParentEdges == { <<m, parent[m]>> : m \in { x \in Node : parent[x] # NoNode } }

AncestorProperties ==
  LET anc == TransClosure(ParentEdges, Node)
  IN  /\ parent[initiator] = NoNode
      /\ \A n \in Node :
           /\ <<n, n>> \notin anc
           /\ parent[n] # NoNode =>
                /\ R[n, parent[n]]
                /\ <<n, initiator>> \in anc

PostCondition ==
  (\A n \in Node : pc[n] = "Done") =>
    LET anc == TransClosure(ParentEdges, Node)
    IN  /\ \A n \in Node : inbox[n] = {}
        /\ parent[initiator] = NoNode
        /\ \A n \in Node \ {initiator} :
             /\ parent[n] \in neighbors(n)
             /\ <<n, initiator>> \in anc
        /\ \A n \in Node : children[n] = { m \in Node : parent[m] = n }

View == << inbox, pc, parent, children, rcvd, nbrs >>

-----------------------------------------------------------------------------
(* Model-checking instance: fully connected mesh of 4 nodes *)

N1 == {"n1", "n2", "n3", "n4"}

I1 == "n1"

R1 == [e \in N1 \X N1 |-> e[1] # e[2]]

TestSpec == Spec

=============================================================================