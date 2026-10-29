------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m,n]}

Reachable(n) ==
  LET RECURSIVE Reach(_)
      Reach(S) == LET S2 == S \cup {m \in Node : \E k \in S : R[k,m]}
                  IN IF S2 = S THEN S ELSE Reach(S2)
  IN Reach({n})

ASSUME
  /\ initiator \in Node
  /\ R \in [Node \X Node -> BOOLEAN]
  /\ \A n \in Node : ~ R[n,n]
  /\ \A m, n \in Node : R[m,n] = R[n,m]
  /\ Reachable(initiator) = Node

Message == [kind : {"m1", "m2"}, sndr : Node]

multicast(box, snd, rcvs, k) ==
  [m \in Node |-> IF m \in rcvs
                  THEN box[m] \cup {[kind |-> k, sndr |-> snd]}
                  ELSE box[m]]

VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ nbrs = [n \in Node |-> neighbors(n)]
  /\ pc = [n \in Node |-> "n0"]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN inbox' = multicast(inbox, self, nbrs[self], "m1")
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(neighbors(self))
       THEN /\ \E msg \in inbox[self] :
                 LET net == [inbox EXCEPT ![self] = @ \ {msg}]
                 IN /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
                    /\ IF self # initiator /\ rcvd[self] = 0
                         THEN /\ msg.kind = "m1"
                              /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                              /\ nbrs' = [nbrs EXCEPT ![self] = @ \ {msg.sndr}]
                              /\ inbox' = multicast(net, self, nbrs[self] \ {msg.sndr}, "m1")
                              /\ UNCHANGED children
                         ELSE /\ inbox' = net
                              /\ children' = IF msg.kind = "m2"
                                               THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                                               ELSE children
                              /\ UNCHANGED << parent, nbrs >>
            /\ UNCHANGED pc
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED << inbox, parent, children, rcvd, nbrs >>

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
       THEN inbox' = multicast(inbox, self, {parent[self]}, "m2")
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

TypeOK ==
  /\ inbox \in [Node -> SUBSET Message]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))

ParentChild ==
  \A m, n \in Node :
     /\ n \in children[m] => m = parent[n]
     /\ (m = parent[n] /\ pc[m] = "Done") => n \in children[m]

Ancestors(n) ==
  LET RECURSIVE A(_)
      A(S) == LET S2 == S \cup {parent[k] : k \in {x \in S : parent[x] # NoNode}}
              IN IF S2 = S THEN S ELSE A(S2)
  IN A(IF parent[n] = NoNode THEN {} ELSE {parent[n]})

AncestorProperties ==
  /\ \A n \in Node : n \notin Ancestors(n)
  /\ \A n \in Node : parent[n] # NoNode => initiator \in Ancestors(n)
  /\ \A n \in Node \ {initiator} : pc[n] = "Done" => initiator \in Ancestors(n)
  /\ parent[initiator] = NoNode

SpanningTree ==
  (\A n \in Node : pc[n] = "Done") =>
     \A n \in Node \ {initiator} : /\ parent[n] \in neighbors(n)
                                   /\ initiator \in Ancestors(n)

=============================================================================