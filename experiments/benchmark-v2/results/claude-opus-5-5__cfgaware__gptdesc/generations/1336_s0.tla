------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* A tiny, fully connected undirected graph with three nodes "a", "b", "c" *)
(* used to model check the Echo algorithm.                                 *)
(***************************************************************************)

CONSTANTS Node, initiator, R

VARIABLES inbox, parent, rcvd, pc

vars == <<inbox, parent, rcvd, pc>>

(***************************************************************************)
(* Properties of relations, represented as functions in [S \X S -> BOOLEAN]*)
(***************************************************************************)
IsIrreflexive(r, S) == \A n \in S : ~ r[n, n]

IsSymmetric(r, S) == \A m, n \in S : r[m, n] = r[n, m]

RECURSIVE ReachFrom(_, _, _)
ReachFrom(r, S, X) ==
  LET Y == X \cup {m \in S : \E n \in X : r[n, m]}
  IN  IF Y = X THEN X ELSE ReachFrom(r, S, Y)

IsConnected(r, S) == \A n \in S : ReachFrom(r, S, {n}) = S

IsFullyConnected(r, S) == \A m, n \in S : m # n => r[m, n]

(***************************************************************************)
(* Model definitions                                                       *)
(***************************************************************************)

\* Explicit set of nodes
N1 == {"a", "b", "c"}

\* The initiator
I1 == "a"

\* The edge relation, chosen by CHOOSE among functions defined by domain
R1 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
          /\ IsConnected(r, N1)
          /\ IsSymmetric(r, N1)
          /\ IsIrreflexive(r, N1)
          /\ IsFullyConnected(r, N1)

(***************************************************************************)
(* The Echo algorithm                                                      *)
(***************************************************************************)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

Init ==
  /\ inbox  = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> NoNode]
  /\ rcvd   = [n \in Node |-> 0]
  /\ pc     = [n \in Node |-> "n0"]

\* The initiator starts by sending a message to all of its neighbors.
Initiate ==
  /\ pc[initiator] = "n0"
  /\ inbox' = [m \in Node |->
                 IF m \in neighbors(initiator)
                 THEN inbox[m] \cup {initiator}
                 ELSE inbox[m]]
  /\ pc' = [pc EXCEPT ![initiator] = "w"]
  /\ UNCHANGED <<parent, rcvd>>

\* A non-initiator receives its first message, adopts the sender as parent,
\* and forwards the message to all other neighbors.
FirstMsg(n) ==
  /\ n # initiator
  /\ pc[n] = "n0"
  /\ \E m \in inbox[n] :
       /\ parent' = [parent EXCEPT ![n] = m]
       /\ rcvd' = [rcvd EXCEPT ![n] = 1]
       /\ inbox' = [k \in Node |->
                      IF k = n THEN inbox[n] \ {m}
                      ELSE IF k \in neighbors(n) \ {m}
                           THEN inbox[k] \cup {n}
                           ELSE inbox[k]]
  /\ pc' = [pc EXCEPT ![n] = "w"]

\* A waiting node receives a further message.
Receive(n) ==
  /\ pc[n] = "w"
  /\ \E m \in inbox[n] :
       /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
       /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
  /\ UNCHANGED <<parent, pc>>

\* Once a node has heard from all neighbors, it echoes to its parent.
Finish(n) ==
  /\ pc[n] = "w"
  /\ rcvd[n] = Cardinality(neighbors(n))
  /\ IF n # initiator
       THEN inbox' = [inbox EXCEPT ![parent[n]] = @ \cup {n}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, rcvd>>

Terminated ==
  /\ \A n \in Node : pc[n] = "done"
  /\ UNCHANGED vars

Next ==
  \/ Initiate
  \/ \E n \in Node : FirstMsg(n) \/ Receive(n) \/ Finish(n)
  \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK ==
  /\ inbox  \in [Node -> SUBSET Node]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ rcvd   \in [Node -> 0 .. Cardinality(Node)]
  /\ pc     \in [Node -> {"n0", "w", "done"}]

RECURSIVE ParentIter(_, _)
ParentIter(n, k) ==
  IF k = 0 \/ parent[n] = NoNode
    THEN {}
    ELSE {parent[n]} \cup ParentIter(parent[n], k - 1)

Ancestors(n) == ParentIter(n, Cardinality(Node))

AncestorProperties ==
  /\ parent[initiator] = NoNode
  /\ \A n \in Node :
       /\ n \notin Ancestors(n)
       /\ parent[n] # NoNode =>
            /\ parent[n] \in neighbors(n)
            /\ initiator \in Ancestors(n)

View == <<inbox, parent, rcvd, pc>>

(***************************************************************************)
(* Test specification and postcondition for TLC                           *)
(***************************************************************************)

TestSpec ==
  /\ PrintT(R1)
  /\ Spec

PostCondition ==
  TLCGet("stats").generated >= TLCGet("stats").distinct

=============================================================================