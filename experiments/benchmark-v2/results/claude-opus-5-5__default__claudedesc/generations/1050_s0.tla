------------------------------- MODULE MCEcho -------------------------------
(***************************************************************************)
(* Model-checking configuration for the Echo algorithm. To keep this       *)
(* module self-contained, the abstract Echo specification is included     *)
(* here, parameterized by the constants Node, initiator, R and NoNode.     *)
(* The MC definitions N1, I1, R1 and R2 supply concrete values for these   *)
(* constants (for example, via a TLC configuration file:                   *)
(*   Node <- N1, initiator <- I1, R <- R1, NoNode = NoNode as model value). *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,       \* set of nodes
          initiator,  \* the node that starts the algorithm
          R,          \* the graph: R[m,n] = TRUE iff there is an edge m--n
          NoNode      \* special value denoting the absence of a node

(***************************************************************************)
(* Graph properties assumed by the Echo algorithm                          *)
(***************************************************************************)
IsIrreflexive(r, S) == \A x \in S : ~ r[x, x]

IsSymmetric(r, S) == \A x, y \in S : r[x, y] = r[y, x]

RECURSIVE ReachSet(_, _, _, _)
ReachSet(r, S, X, k) ==
  IF k = 0 THEN X
  ELSE ReachSet(r, S, X \cup {y \in S : \E x \in X : r[x, y]}, k - 1)

IsConnected(r, S) ==
  \A x \in S : ReachSet(r, S, {x}, Cardinality(S)) = S

ASSUME /\ IsFiniteSet(Node)
       /\ initiator \in Node
       /\ NoNode \notin Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

neighbors(n) == {m \in Node : R[m, n]}

Msg == [kind : {"explore", "echo"}, sndr : Node]

(***************************************************************************)
(* Echo algorithm                                                          *)
(***************************************************************************)
VARIABLES inbox,     \* inbox[n]: set of messages pending at node n
          parent,    \* parent[n]: parent of n in the spanning tree
          children,  \* children[n]: children of n in the spanning tree
          rcvd,      \* rcvd[n]: number of messages received by n
          nbrs,      \* nbrs[n]: neighbors of n
          pc         \* control state of each node

vars == <<inbox, parent, children, rcvd, nbrs, pc>>

Multicast(box, s, targets, k) ==
  [n \in Node |-> IF n \in targets
                    THEN box[n] \cup {[kind |-> k, sndr |-> s]}
                    ELSE box[n]]

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ pc \in [Node -> {"n0", "n1", "done"}]

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ nbrs = [n \in Node |-> neighbors(n)]
  /\ pc = [n \in Node |-> "n0"]

\* The initiator starts by sending explorer messages to all its neighbors.
Start(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN /\ inbox' = Multicast(inbox, self, nbrs[self], "explore")
            /\ parent' = [parent EXCEPT ![self] = self]
       ELSE UNCHANGED <<inbox, parent>>
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED <<children, rcvd, nbrs>>

\* Receive a message. The first message received by a non-initiator node
\* determines its parent; it then forwards explorers to all other neighbors.
Receive(self) ==
  /\ pc[self] = "n1"
  /\ rcvd[self] < Cardinality(nbrs[self])
  /\ \E msg \in inbox[self] :
       LET box1 == [inbox EXCEPT ![self] = @ \ {msg}]
       IN  /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
           /\ IF parent[self] = NoNode
                THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                     /\ inbox' = Multicast(box1, self,
                                           nbrs[self] \ {msg.sndr}, "explore")
                     /\ UNCHANGED children
                ELSE /\ inbox' = box1
                     /\ UNCHANGED parent
                     /\ children' =
                          IF msg.kind = "echo"
                            THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                            ELSE children
  /\ UNCHANGED <<nbrs, pc>>

\* Once messages from all neighbors have been received, a non-initiator
\* node sends an echo to its parent and terminates.
Finish(self) ==
  /\ pc[self] = "n1"
  /\ rcvd[self] = Cardinality(nbrs[self])
  /\ inbox' = IF self # initiator
                THEN Multicast(inbox, self, {parent[self]}, "echo")
                ELSE inbox
  /\ pc' = [pc EXCEPT ![self] = "done"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

node(self) == Start(self) \/ Receive(self) \/ Finish(self)

Terminating ==
  /\ \A n \in Node : pc[n] = "done"
  /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
RECURSIVE anc(_, _)
anc(n, k) ==
  IF k = 0 \/ parent[n] = NoNode \/ parent[n] = n
    THEN {}
    ELSE {parent[n]} \cup anc(parent[n], k - 1)

Ancestors(n) == anc(n, Cardinality(Node))

AncestorProperties ==
  \A n \in Node :
    parent[n] # NoNode =>
      /\ n # initiator =>
           /\ initiator \in Ancestors(n)
           /\ n \notin Ancestors(n)
      /\ \A c \in children[n] : parent[c] = n

Termination == <>(\A n \in Node : pc[n] = "done")

(***************************************************************************)
(* Model-checking definitions                                              *)
(***************************************************************************)
N1 == {"a", "b", "c"}

\* The initiator is chosen arbitrarily.
I1 == CHOOSE n \in N1 : TRUE

\* Complete graph without self-loops.
R1 == [edge \in N1 \X N1 |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

\* Alternatively, any graph satisfying the assumptions of the algorithm.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Specification with diagnostic output of the graph at startup.
SpecWithPrint == /\ PrintT(<<"Graph", R>>)
                 /\ Spec

=============================================================================