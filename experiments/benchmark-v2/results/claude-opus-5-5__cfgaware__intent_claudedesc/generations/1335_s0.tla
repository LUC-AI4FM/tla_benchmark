---------------------------- MODULE Echo ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m,n] }

TC(r) ==
  LET Iter[k \in Nat] ==
        IF k = 0 THEN r
        ELSE Iter[k-1] \cup
             { p \in Node \X Node :
                 \E b \in Node : <<p[1], b>> \in Iter[k-1] /\ <<b, p[2]>> \in r }
  IN  Iter[Cardinality(Node)]

GraphEdges == { p \in Node \X Node : R[p[1], p[2]] }

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ \A n \in Node : ~ R[n,n]
       /\ \A m, n \in Node : R[m,n] = R[n,m]
       /\ \A m, n \in Node : m # n => <<m, n>> \in TC(GraphEdges)

Message == [kind : {"m", "c"}, sndr : Node]

VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

multicast(ib, dests, snd, k) ==
  [n \in Node |-> IF n \in dests
                  THEN ib[n] \cup {[kind |-> k, sndr |-> snd]}
                  ELSE ib[n]]

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
       THEN inbox' = multicast(inbox, nbrs[self], self, "m")
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(nbrs[self])
       THEN \E msg \in inbox[self] :
              /\ IF msg.kind = "m" /\ rcvd[self] = 0 /\ self # initiator
                   THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                        /\ LET ib == [inbox EXCEPT ![self] = @ \ {msg}]
                           IN inbox' = multicast(ib, nbrs[self] \ {msg.sndr}, self, "m")
                   ELSE /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                        /\ UNCHANGED parent
              /\ IF msg.kind = "c"
                   THEN children' = [children EXCEPT ![self] = @ \cup {msg.sndr}]
                   ELSE UNCHANGED children
              /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
              /\ pc' = pc
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED << inbox, parent, children, rcvd >>
  /\ UNCHANGED nbrs

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
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

TypeOK ==
  /\ parent \in [Node -> (Node \cup {NoNode})]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n)
  /\ inbox \in [Node -> SUBSET Message]
  /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]

AllDone == \A n \in Node : pc[n] = "Done"

ParentProperties ==
  /\ parent[initiator] = NoNode
  /\ AllDone => \A n \in Node \ {initiator} : parent[n] \in neighbors(n)
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode => parent[n] \in neighbors(n)

ParentChild ==
  AllDone =>
    \A m, n \in Node : (n \in children[m]) <=> (m # NoNode /\ parent[n] = m)

ParentRel == { p \in Node \X Node : parent[p[2]] = p[1] }

Ancestor == TC(ParentRel)

AncestorProperties ==
  AllDone =>
    /\ \A n \in Node \ {initiator} : <<initiator, n>> \in Ancestor
    /\ \A n \in Node : <<n, n>> \notin Ancestor

=============================================================================