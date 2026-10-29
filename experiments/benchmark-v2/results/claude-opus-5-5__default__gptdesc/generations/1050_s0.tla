------------------------------- MODULE MCEcho -------------------------------
(***************************************************************************)
(* Model-checking instantiation of the Echo algorithm.  It uses a tiny     *)
(* three-node graph and picks the initiator nondeterministically from      *)
(* those nodes.  It gives two concrete graphs: R1, written explicitly as a *)
(* function over node pairs, and R2, chosen to satisfy the connectivity,   *)
(* symmetry and irreflexivity assumptions.  The Echo algorithm itself is   *)
(* written out below, so the module parses without an external Echo file. *)
(* It also defines a test specification, a view and a postcondition that  *)
(* use TLC-specific operators.                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Graph utilities. A graph is a function [N \X N -> BOOLEAN].             *)
(***************************************************************************)
IsIrreflexive(r, N) == \A n \in N : ~ r[n, n]

IsSymmetric(r, N) == \A m, n \in N : r[m, n] = r[n, m]

ReachableFrom(r, N, n) ==
    LET RECURSIVE Reach(_, _)
        Reach(S, k) == IF k = 0 THEN S
                       ELSE Reach(S \cup {y \in N : \E x \in S : r[x, y]}, k - 1)
    IN  Reach({n}, Cardinality(N))

IsConnected(r, N) == \A m, n \in N : n \in ReachableFrom(r, N, m)

(***************************************************************************)
(* Concrete model values.                                                  *)
(***************************************************************************)
N1 == {1, 2, 3}

\* Initiator chosen nondeterministically among the nodes.
I1 == CHOOSE n \in N1 : TRUE

\* A graph given explicitly as a function over node pairs (a line 1-2-3).
R1 == [ e \in N1 \X N1 |-> e \in {<<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>} ]

\* A graph chosen to satisfy the assumptions of the Echo algorithm.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
          /\ IsConnected(r, N1)
          /\ IsSymmetric(r, N1)
          /\ IsIrreflexive(r, N1)

(***************************************************************************)
(* Instantiated parameters of the Echo algorithm.                          *)
(***************************************************************************)
Node      == N1
initiator == I1
R         == R2

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x \in 0..Cardinality(Node) : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

Msg == [kind : {"m", "c"}, sndr : Node]

(***************************************************************************)
(* The Echo algorithm.                                                     *)
(***************************************************************************)
VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == <<inbox, pc, parent, children, rcvd, nbrs>>

TypeOK ==
    /\ inbox \in [Node -> SUBSET Msg]
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]

Init ==
    /\ inbox = [n \in Node |-> {}]
    /\ pc = [n \in Node |-> "n0"]
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ rcvd = [n \in Node |-> 0]
    /\ nbrs = [n \in Node |-> neighbors(n)]

\* The initiator starts by sending an explorer message to all neighbors.
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF self = initiator
         THEN inbox' = [n \in Node |->
                          IF n \in nbrs[self]
                            THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                            ELSE inbox[n]]
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED <<parent, children, rcvd, nbrs>>

\* Receive messages until one has arrived from every neighbor.
n1(self) ==
    /\ pc[self] = "n1"
    /\ IF rcvd[self] < Cardinality(nbrs[self])
         THEN \E msg \in inbox[self] :
                /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
                /\ IF self # initiator /\ rcvd[self] = 0
                     THEN \* first message: adopt the sender as parent
                          /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                          /\ inbox' = [n \in Node |->
                                IF n = self THEN inbox[self] \ {msg}
                                ELSE IF n \in nbrs[self] \ {msg.sndr}
                                     THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                     ELSE inbox[n]]
                          /\ UNCHANGED children
                     ELSE /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                          /\ children' = IF msg.kind = "c"
                                           THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                                           ELSE children
                          /\ UNCHANGED parent
                /\ UNCHANGED <<pc, nbrs>>
         ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
              /\ UNCHANGED <<inbox, parent, children, rcvd, nbrs>>

\* Non-initiators echo back to their parent.
n2(self) ==
    /\ pc[self] = "n2"
    /\ IF self # initiator
         THEN inbox' = [inbox EXCEPT ![parent[self]] =
                          @ \cup {[kind |-> "c", sndr |-> self]}]
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<parent, children, rcvd, nbrs>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminated == \A n \in Node : pc[n] = "Done"

Terminating == Terminated /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
RECURSIVE Ancestor(_, _)
Ancestor(n, k) == IF k = 0 \/ n = NoNode THEN n ELSE Ancestor(parent[n], k - 1)

InitiatorHasNoParent == parent[initiator] = NoNode

ParentIsNeighbor ==
    \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

\* On termination, the parent pointers form a spanning tree rooted at the
\* initiator, and the children sets match the parent pointers.
SpanningTree ==
    Terminated =>
      /\ \A n \in Node \ {initiator} : parent[n] \in neighbors(n)
      /\ \A n \in Node : \E k \in 0..Cardinality(Node) : Ancestor(n, k) = initiator
      /\ \A n \in Node : children[n] = {m \in Node : parent[m] = n}

Termination == <>Terminated

(***************************************************************************)
(* TLC-specific definitions.                                               *)
(***************************************************************************)
\* Print the relation at startup, then run the Echo specification.
TestSpec == PrintT(<<"R", R>>) /\ Spec

\* View: nbrs is constant, so it is left out of the view.
MCView == <<inbox, pc, parent, children, rcvd>>

\* Postcondition: report the statistics and require that some states were explored.
MCPostCondition ==
    /\ PrintT(<<"stats", TLCGet("stats")>>)
    /\ TLCGet("stats").distinct > 0
=============================================================================