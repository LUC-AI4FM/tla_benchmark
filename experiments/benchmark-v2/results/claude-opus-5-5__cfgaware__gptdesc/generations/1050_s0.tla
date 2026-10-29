------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Parameters of the echo protocol.                                        *)
(***************************************************************************)
CONSTANTS Node, initiator, R

(***************************************************************************)
(* Graph helper operators.                                                 *)
(***************************************************************************)
IsIrreflexive(r, S) == \A n \in S : ~ r[n, n]

IsSymmetric(r, S) == \A m, n \in S : r[m, n] = r[n, m]

Reachable(r, S, from) ==
  LET RECURSIVE Expand(_, _)
      Expand(X, k) ==
        IF k = 0 THEN X
        ELSE Expand(X \cup {y \in S : \E x \in X : r[x, y]}, k - 1)
  IN  Expand({from}, Cardinality(S))

IsConnected(r, S) == \A m, n \in S : n \in Reachable(r, S, m)

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

(***************************************************************************)
(* The echo protocol.                                                      *)
(***************************************************************************)
VARIABLES inbox, rcvd, parent, phase

vars == <<inbox, rcvd, parent, phase>>

Phases == {"start", "idle", "wait", "done"}

TypeOK ==
  /\ inbox \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> Phases]

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> IF n = initiator THEN "start" ELSE "idle"]

\* The initiator sends the explorer message to all of its neighbors.
Start ==
  /\ phase[initiator] = "start"
  /\ inbox' = [k \in Node |-> IF k \in neighbors(initiator)
                                THEN inbox[k] \cup {initiator}
                                ELSE inbox[k]]
  /\ phase' = [phase EXCEPT ![initiator] = "wait"]
  /\ UNCHANGED <<rcvd, parent>>

\* Node n receives a message from m.
Receive(n, m) ==
  /\ m \in inbox[n]
  /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
  /\ IF phase[n] = "idle"
       THEN /\ parent' = [parent EXCEPT ![n] = m]
            /\ phase' = [phase EXCEPT ![n] = "wait"]
            /\ inbox' = [k \in Node |->
                           IF k = n THEN inbox[k] \ {m}
                           ELSE IF k \in neighbors(n) \ {m}
                                  THEN inbox[k] \cup {n}
                                  ELSE inbox[k]]
       ELSE /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
            /\ UNCHANGED <<parent, phase>>

\* Node n has heard from all neighbors: echo to the parent and terminate.
Finish(n) ==
  /\ phase[n] = "wait"
  /\ rcvd[n] = Cardinality(neighbors(n))
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ inbox' = IF n = initiator THEN inbox
              ELSE [inbox EXCEPT ![parent[n]] = @ \cup {n}]
  /\ UNCHANGED <<rcvd, parent>>

Next ==
  \/ Start
  \/ \E n \in Node : \E m \in Node : Receive(n, m)
  \/ \E n \in Node : Finish(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
RECURSIVE Ancs(_, _)
Ancs(n, k) ==
  IF k = 0 \/ parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Ancs(parent[n], k - 1)

AncestorProperties ==
  \A n \in Node :
    /\ parent[n] # NoNode => initiator \in Ancs(n, Cardinality(Node))
    /\ n \notin Ancs(n, Cardinality(Node))

Termination == <>(\A n \in Node : phase[n] = "done")

(***************************************************************************)
(* Model-checking instantiation.                                           *)
(***************************************************************************)
N1 == {"a", "b", "c"}

\* Choose the initiator nondeterministically among the nodes.
I1 == CHOOSE n \in N1 : TRUE

\* A graph given explicitly as a function over node pairs.
R0 == [e \in N1 \X N1 |->
         e \in {<<"a", "b">>, <<"b", "a">>, <<"b", "c">>, <<"c", "b">>}]

\* A graph chosen to satisfy the assumptions of the protocol.
R1 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ IsIrreflexive(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsConnected(r, N1)

TestSpec == PrintT(<<"R", R>>) /\ Spec

MCView == <<inbox, rcvd, parent, phase>>

PostCondition == TLCGet("stats").distinct > 0

=============================================================================