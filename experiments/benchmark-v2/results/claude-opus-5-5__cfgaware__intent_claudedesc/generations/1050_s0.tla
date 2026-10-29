------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, root of the spanning tree
          R          \* neighborhood relation, a Boolean function over Node \X Node

-----------------------------------------------------------------------------
(* Relation helpers *)

IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

RECURSIVE Reach(_, _, _)
Reach(rel, S, k) ==
  IF k = 0 THEN S
  ELSE Reach(rel, S \cup { y \in DOMAIN rel : FALSE }, 0)

\* Set of nodes reachable from x in at most k steps
RECURSIVE ReachFrom(_, _, _, _)
ReachFrom(rel, Nodes, Front, k) ==
  IF k = 0 THEN Front
  ELSE ReachFrom(rel, Nodes,
                 Front \cup { y \in Nodes : \E x \in Front : rel[x, y] },
                 k - 1)

IsConnected(rel, S) ==
  \A x \in S : ReachFrom(rel, S, {x}, Cardinality(S)) = S

-----------------------------------------------------------------------------
(* Concrete model instance used by the model-checking configuration *)

N1 == {"a", "b", "c", "d"}

I1 == "a"

\* fully-connected (mesh) topology
R1 == [e \in N1 \X N1 |-> e[1] # e[2]]

-----------------------------------------------------------------------------

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x \in {"NoNode", "noNode"} : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

Message == [kind : {"m", "c"}, sndr : Node]

send(box, i, j, k) == [box EXCEPT ![j] = @ \cup {[kind |-> k, sndr |-> i]}]

multicast(box, i, S, k) ==
  [m \in Node |-> IF m \in S THEN box[m] \cup {[kind |-> k, sndr |-> i]}
                             ELSE box[m]]

-----------------------------------------------------------------------------

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
        THEN inbox' = multicast(inbox, self, nbrs[self], "m")
        ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(nbrs[self])
        THEN \E msg \in inbox[self] :
               /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
               /\ IF self # initiator /\ rcvd[self] + 1 = 1
                     THEN /\ Assert(msg.kind = "m", "first message must be m")
                          /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                          /\ inbox' = [multicast(inbox, self,
                                          nbrs[self] \ {msg.sndr}, "m")
                                         EXCEPT ![self] = @ \ {msg}]
                          /\ UNCHANGED children
                     ELSE /\ IF msg.kind = "c"
                                THEN children' = [children EXCEPT
                                                    ![self] = @ \cup {msg.sndr}]
                                ELSE UNCHANGED children
                          /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                          /\ UNCHANGED parent
               /\ pc' = [pc EXCEPT ![self] = "n1"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
             /\ UNCHANGED << inbox, parent, children, rcvd >>
  /\ UNCHANGED nbrs

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
        THEN /\ Assert(parent[self] \in nbrs[self], "parent must be a neighbor")
             /\ inbox' = send(inbox, self, parent[self], "c")
        ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A self \in Node : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

TestSpec == Spec

Termination == <>(\A self \in Node : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Correctness properties *)

TypeOK ==
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ inbox \in [Node -> SUBSET Message]
  /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
  /\ parent \in [Node -> (Node \cup {NoNode})]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])

RECURSIVE Anc(_, _)
Anc(n, k) ==
  IF k = 0 \/ parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Anc(parent[n], k - 1)

Ancestors(n) == Anc(n, Cardinality(Node))

AncestorProperties ==
  /\ parent[initiator] = NoNode
  /\ \A n \in Node :
       /\ parent[n] # NoNode => parent[n] \in neighbors(n)
       /\ n \notin Ancestors(n)
       /\ (n # initiator /\ parent[n] # NoNode) => initiator \in Ancestors(n)
       /\ \A c \in children[n] : parent[c] = n
       /\ (pc[n] \in {"n2", "Done"} /\ n # initiator) => parent[n] # NoNode

\* Initiator only completes after all nodes finished their local processing
Acknowledged ==
  pc[initiator] = "Done" =>
    \A n \in Node : /\ pc[n] = "Done"
                    /\ n # initiator => parent[n] # NoNode

=============================================================================