------------------------------- MODULE Echo -------------------------------
(***************************************************************************)
(* The Echo algorithm for constructing a spanning tree in an undirected,   *)
(* connected graph.  A designated initiator floods "m" (exploration)       *)
(* messages; every non-initiator adopts the sender of its first message as *)
(* its parent, forwards "m" to all other neighbors, and after having heard *)
(* from all neighbors it echoes a "c" (child confirmation) message back to *)
(* its parent.  The initiator terminates once all neighbors have answered. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, NoNode

ASSUME NoNode \notin Node
ASSUME Node # {} /\ IsFiniteSet(Node)

\* The designated initiator (root of the spanning tree).
initiator == CHOOSE n \in Node : TRUE

\* The undirected communication graph: here the complete graph over Node,
\* which is connected and has no self-loops.
R == [p \in Node \X Node |-> p[1] # p[2]]

neighbors(n) == {m \in Node : R[<<m, n>>]}

\* Graph sanity conditions
ASSUME \A m, n \in Node : R[<<m, n>>] = R[<<n, m>>]     \* undirected
ASSUME \A n \in Node : ~ R[<<n, n>>]                    \* no self-loops

\* Connectivity: every node is reachable from the initiator.
RECURSIVE Reach(_, _)
Reach(S, k) == IF k = 0 THEN S
               ELSE Reach(S \cup UNION {neighbors(x) : x \in S}, k - 1)
ASSUME Reach({initiator}, Cardinality(Node)) = Node

Msg == [kind : {"m", "c"}, sndr : Node]

VARIABLES inbox, rcvd, parent, children, pc

vars == <<inbox, rcvd, parent, children, pc>>

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ rcvd \in [Node -> 0 .. Cardinality(Node)]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ pc \in [Node -> {"start", "wait", "done"}]

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ pc = [n \in Node |-> "start"]

\* Send message msg to every node in set S.
SendAll(ib, S, msg) == [k \in Node |-> IF k \in S THEN ib[k] \cup {msg} ELSE ib[k]]

\* The initiator starts by sending "m" to all its neighbors.
InitiatorStart ==
  /\ pc[initiator] = "start"
  /\ inbox' = SendAll(inbox, neighbors(initiator), [kind |-> "m", sndr |-> initiator])
  /\ pc' = [pc EXCEPT ![initiator] = "wait"]
  /\ UNCHANGED <<rcvd, parent, children>>

\* A non-initiator receives its first message and adopts the sender as parent.
ReceiveFirst(n) ==
  /\ n # initiator
  /\ pc[n] = "start"
  /\ \E msg \in inbox[n] :
       /\ parent' = [parent EXCEPT ![n] = msg.sndr]
       /\ rcvd' = [rcvd EXCEPT ![n] = 1]
       /\ inbox' = SendAll([inbox EXCEPT ![n] = @ \ {msg}],
                           neighbors(n) \ {msg.sndr},
                           [kind |-> "m", sndr |-> n])
  /\ pc' = [pc EXCEPT ![n] = "wait"]
  /\ UNCHANGED children

\* A node waiting for further messages receives one.
Receive(n) ==
  /\ pc[n] = "wait"
  /\ rcvd[n] < Cardinality(neighbors(n))
  /\ \E msg \in inbox[n] :
       /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg}]
       /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
       /\ children' = IF msg.kind = "c"
                        THEN [children EXCEPT ![n] = @ \cup {msg.sndr}]
                        ELSE children
  /\ UNCHANGED <<parent, pc>>

\* A node that has heard from all neighbors completes; a non-initiator
\* confirms the child relationship to its parent.
Finish(n) ==
  /\ pc[n] = "wait"
  /\ rcvd[n] = Cardinality(neighbors(n))
  /\ inbox' = IF n = initiator THEN inbox
              ELSE [inbox EXCEPT ![parent[n]] = @ \cup {[kind |-> "c", sndr |-> n]}]
  /\ pc' = [pc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<rcvd, parent, children>>

Proc(n) ==
  \/ (n = initiator /\ InitiatorStart)
  \/ ReceiveFirst(n)
  \/ Receive(n)
  \/ Finish(n)

Terminated == \A n \in Node : pc[n] = "done"

Next == (\E n \in Node : Proc(n))
        \/ (Terminated /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ \A n \in Node : WF_vars(Proc(n))

---------------------------------------------------------------------------
(* Correctness properties *)

Termination == <>Terminated

ParentNeighbor ==
  \A n \in Node \ {initiator} :
     pc[n] = "done" => (parent[n] \in Node /\ parent[n] \in neighbors(n))

InitiatorNoParent == parent[initiator] = NoNode

ParentChildConsistency ==
  Terminated =>
    \A m, n \in Node : (n \in children[m]) <=> (n # initiator /\ parent[n] = m)

RECURSIVE Anc(_, _)
Anc(n, k) == IF k = 0 \/ parent[n] = NoNode THEN {}
             ELSE {parent[n]} \cup Anc(parent[n], k - 1)

Ancestors(n) == Anc(n, Cardinality(Node))

AncestorProperties ==
  Terminated =>
    /\ \A n \in Node : n \notin Ancestors(n)
    /\ \A n \in Node \ {initiator} : initiator \in Ancestors(n)

=============================================================================