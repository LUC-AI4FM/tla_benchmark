---------------------------- MODULE Echo ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R

\* Graph properties of the neighborhood relation R
IsIrreflexive(rel, S) == \A n \in S : ~ rel[n, n]

IsSymmetric(rel, S) == \A m, n \in S : rel[m, n] = rel[n, m]

RECURSIVE ReachSet(_, _, _)
ReachSet(rel, S, Nodes) ==
  LET T == S \cup {m \in Nodes : \E k \in S : rel[k, m]}
  IN  IF T = S THEN S ELSE ReachSet(rel, T, Nodes)

IsConnected(rel, S) == \A n \in S : ReachSet(rel, {n}, S) = S

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

vars == <<inbox, pc, parent, children, rcvd, nbrs>>

-----------------------------------------------------------------------------

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ pc = [n \in Node |-> "n0"]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ nbrs = [n \in Node |-> neighbors(n)]

\* Phase 1: the initiator multicasts "m" to all its neighbors
n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN inbox' = [m \in Node |->
                        IF m \in nbrs[self]
                          THEN inbox[m] \cup {[kind |-> "m", sndr |-> self]}
                          ELSE inbox[m]]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

\* Phase 2: receive messages until one has been received from every neighbor
n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(nbrs[self])
       THEN \E msg \in inbox[self] :
              /\ IF msg.kind = "m" /\ rcvd[self] = 0 /\ self # initiator
                   THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                        /\ inbox' = [m \in Node |->
                                       IF m \in nbrs[self] \ {msg.sndr}
                                         THEN inbox[m] \cup {[kind |-> "m", sndr |-> self]}
                                         ELSE IF m = self
                                                THEN inbox[self] \ {msg}
                                                ELSE inbox[m]]
                        /\ UNCHANGED children
                   ELSE /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                        /\ children' = IF msg.kind = "c"
                                         THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                                         ELSE children
                        /\ UNCHANGED parent
              /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
              /\ pc' = pc
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED <<inbox, parent, children, rcvd>>
  /\ UNCHANGED nbrs

\* Phase 3: non-initiators acknowledge their parent with a "c" message
n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
       THEN inbox' = [inbox EXCEPT ![parent[self]] =
                        @ \cup {[kind |-> "c", sndr |-> self]}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A n \in Node : pc[n] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])

InitiatorNoParent == parent[initiator] = NoNode

ParentIsNeighbor ==
  \A n \in Node : parent[n] \in Node => parent[n] \in neighbors(n)

ParentChildConsistent ==
  /\ \A m, n \in Node : m \in children[n] => parent[m] = n
  /\ (\A n \in Node : pc[n] = "Done") =>
        \A m, n \in Node : parent[m] = n => m \in children[n]

RECURSIVE AncSet(_)
AncSet(S) ==
  LET T == S \cup {parent[x] : x \in {y \in S : parent[y] \in Node}}
  IN  IF T = S THEN S ELSE AncSet(T)

Ancestors(n) ==
  AncSet(IF parent[n] \in Node THEN {parent[n]} ELSE {})

AncestorProperties ==
  (\A n \in Node : pc[n] = "Done") =>
     /\ \A n \in Node \ {initiator} : initiator \in Ancestors(n)
     /\ \A n \in Node : n \notin Ancestors(n)

\* Liveness property

Termination == <>(\A n \in Node : pc[n] = "Done")

THEOREM Spec => []TypeOK /\ []InitiatorNoParent /\ []ParentIsNeighbor
                /\ []ParentChildConsistent /\ []AncestorProperties
                /\ Termination
=============================================================================