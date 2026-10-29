------------------------------ MODULE EchoTiny ------------------------------
(***************************************************************************)
(* A tiny, fully connected, undirected graph with three nodes "a", "b",    *)
(* "c" for use with the Echo algorithm. It is meant for model checking and *)
(* demonstration, not for generality. The Echo algorithm is included here  *)
(* so that the module can be parsed and checked on its own.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Initiator

VARIABLES inbox,   \* inbox[n] : set of nodes whose message n has not yet received
          rcvd,    \* rcvd[n]  : number of messages n has received
          parent,  \* parent[n]: the node from which n first heard (root: itself)
          pc       \* pc[n]    : "idle", "waiting" or "done"

vars == <<inbox, rcvd, parent, pc>>

(***************************************************************************)
(* Ways to define the set of nodes.                                        *)
(***************************************************************************)
\* An explicit set.
N1 == {"a", "b", "c"}

\* The domain of a function.
N2 == DOMAIN [a |-> 1, b |-> 2, c |-> 3]

Node == N1

ASSUME N1 = N2
ASSUME Initiator \in Node

NoNode == CHOOSE x : x \notin Node

(***************************************************************************)
(* Properties of relations, which are functions [S \X S -> BOOLEAN].       *)
(***************************************************************************)
IsIrreflexive(R, S) == \A n \in S : ~ R[n, n]

IsSymmetric(R, S) == \A m, n \in S : R[m, n] = R[n, m]

IsConnected(R, S) ==
  LET reach[k \in 0..Cardinality(S)] ==
        IF k = 0
          THEN [p \in S \X S |-> p[1] = p[2]]
          ELSE [p \in S \X S |->
                  \/ reach[k-1][p]
                  \/ \E z \in S : reach[k-1][<<p[1], z>>] /\ R[z, p[2]]]
  IN  \A p \in S \X S : reach[Cardinality(S)][p]

(***************************************************************************)
(* Ways to define the edge relation.                                       *)
(***************************************************************************)
\* An explicit, fully connected relation.
R1 == [e \in Node \X Node |-> e[1] # e[2]]

\* A relation chosen to be connected, symmetric and irreflexive.
R2 == CHOOSE r \in [Node \X Node -> BOOLEAN] :
          /\ IsConnected(r, Node)
          /\ IsSymmetric(r, Node)
          /\ IsIrreflexive(r, Node)

R == R2

ASSUME IsIrreflexive(R1, Node) /\ IsSymmetric(R1, Node) /\ IsConnected(R1, Node)

Neighbors(n) == {m \in Node : R[n, m]}

(***************************************************************************)
(* The Echo algorithm.                                                     *)
(***************************************************************************)
TypeOK ==
  /\ inbox \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ pc \in [Node -> {"idle", "waiting", "done"}]

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ parent = [n \in Node |-> NoNode]
  /\ pc = [n \in Node |-> "idle"]

\* The initiator starts by sending a message to all its neighbors.
Start ==
  /\ pc[Initiator] = "idle"
  /\ pc' = [pc EXCEPT ![Initiator] = "waiting"]
  /\ parent' = [parent EXCEPT ![Initiator] = Initiator]
  /\ inbox' = [m \in Node |->
                 IF m \in Neighbors(Initiator) THEN inbox[m] \cup {Initiator}
                                               ELSE inbox[m]]
  /\ UNCHANGED rcvd

\* Node n receives a message from m. The first message wakes n up, which
\* then records m as its parent and forwards to all other neighbors.
Receive(n, m) ==
  /\ m \in inbox[n]
  /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
  /\ IF pc[n] = "idle"
       THEN /\ pc' = [pc EXCEPT ![n] = "waiting"]
            /\ parent' = [parent EXCEPT ![n] = m]
            /\ inbox' = [k \in Node |->
                           IF k = n THEN inbox[n] \ {m}
                           ELSE IF k \in Neighbors(n) \ {m}
                                  THEN inbox[k] \cup {n}
                                  ELSE inbox[k]]
       ELSE /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
            /\ UNCHANGED <<pc, parent>>

\* Once n has heard from all its neighbors, it echoes to its parent.
Finish(n) ==
  /\ pc[n] = "waiting"
  /\ rcvd[n] = Cardinality(Neighbors(n))
  /\ pc' = [pc EXCEPT ![n] = "done"]
  /\ inbox' = IF n # Initiator
                THEN [inbox EXCEPT ![parent[n]] = @ \cup {n}]
                ELSE inbox
  /\ UNCHANGED <<rcvd, parent>>

Terminated ==
  /\ \A n \in Node : pc[n] = "done"
  /\ UNCHANGED vars

Next ==
  \/ Start
  \/ \E n \in Node : \E m \in Node : Receive(n, m)
  \/ \E n \in Node : Finish(n)
  \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
RcvdBound == \A n \in Node : rcvd[n] <= Cardinality(Neighbors(n))

ParentIsNeighbor ==
  \A n \in Node \ {Initiator} :
     parent[n] # NoNode => parent[n] \in Neighbors(n)

Inv == TypeOK /\ RcvdBound /\ ParentIsNeighbor

Termination == <>(\A n \in Node : pc[n] = "done")

(***************************************************************************)
(* Test specification: print the chosen relation and run Echo's Spec.      *)
(***************************************************************************)
TestSpec == PrintT(R) /\ Spec

\* Postcondition checked by TLC after model checking.
PostCondition ==
  /\ \A n \in Node : pc[n] = "done"
  /\ \A n \in Node : inbox[n] = {}
  /\ parent[Initiator] = Initiator
  /\ \A n \in Node \ {Initiator} : parent[n] \in Neighbors(n)
=============================================================================