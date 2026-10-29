------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

VARIABLES inbox, pc, parent, rcvd

vars == <<inbox, pc, parent, rcvd>>

(***************************************************************************)
(* Concrete values for model checking                                      *)
(***************************************************************************)
N1 == {"a", "b", "c"}

I1 == CHOOSE n \in N1 : TRUE

\* Complete graph on N1 without self-loops
R1 == [edge \in N1 \X N1 |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

(***************************************************************************)
(* Graph properties assumed by the Echo algorithm                          *)
(***************************************************************************)
RECURSIVE ReachFrom(_, _, _, _)
ReachFrom(S, r, Nodes, k) ==
    IF k = 0 THEN S
    ELSE ReachFrom(S \cup {y \in Nodes : \E x \in S : r[x, y]}, r, Nodes, k - 1)

IsConnected(r, Nodes) ==
    \A m \in Nodes : ReachFrom({m}, r, Nodes, Cardinality(Nodes)) = Nodes

IsSymmetric(r, Nodes) ==
    \A m, n \in Nodes : r[m, n] = r[n, m]

IsIrreflexive(r, Nodes) ==
    \A n \in Nodes : ~ r[n, n]

\* Alternative graph: any graph satisfying the Echo assumptions
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
          /\ IsConnected(r, N1)
          /\ IsSymmetric(r, N1)
          /\ IsIrreflexive(r, N1)

ASSUME /\ initiator \in Node
       /\ NoNode \notin Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsConnected(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsIrreflexive(R, Node)

(***************************************************************************)
(* The Echo algorithm                                                      *)
(***************************************************************************)
neighbors(n) == {m \in Node : R[m, n]}

\* inbox[n] is the set of nodes whose (pending) message is in n's inbox.
\* At most one message travels along each directed edge.
SendAll(ib, from, targets) ==
    [m \in Node |-> IF m \in targets THEN ib[m] \cup {from} ELSE ib[m]]

Init ==
    /\ inbox  = [n \in Node |-> {}]
    /\ pc     = [n \in Node |-> IF n = initiator THEN "start" ELSE "idle"]
    /\ parent = [n \in Node |-> NoNode]
    /\ rcvd   = [n \in Node |-> {}]

Start ==
    /\ pc[initiator] = "start"
    /\ inbox' = SendAll(inbox, initiator, neighbors(initiator))
    /\ pc' = [pc EXCEPT ![initiator] = "active"]
    /\ UNCHANGED <<parent, rcvd>>

Receive(n, m) ==
    /\ m \in inbox[n]
    /\ pc[n] \in {"idle", "active"}
    /\ IF pc[n] = "idle"
         THEN /\ parent' = [parent EXCEPT ![n] = m]
              /\ pc' = [pc EXCEPT ![n] = "active"]
              /\ inbox' = SendAll([inbox EXCEPT ![n] = @ \ {m}],
                                  n, neighbors(n) \ {m})
         ELSE /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
              /\ UNCHANGED <<parent, pc>>
    /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {m}]

Finish(n) ==
    /\ pc[n] = "active"
    /\ rcvd[n] = neighbors(n)
    /\ pc' = [pc EXCEPT ![n] = "done"]
    /\ inbox' = IF n = initiator THEN inbox
                ELSE [inbox EXCEPT ![parent[n]] = @ \cup {n}]
    /\ UNCHANGED <<parent, rcvd>>

Next ==
    \/ Start
    \/ \E n \in Node : \E m \in Node : Receive(n, m)
    \/ \E n \in Node : Finish(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TestSpec == PrintT(<<"Graph", R>>) /\ Spec

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ inbox  \in [Node -> SUBSET Node]
    /\ pc     \in [Node -> {"start", "idle", "active", "done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ rcvd   \in [Node -> SUBSET Node]

RECURSIVE Ancestors(_, _)
Ancestors(n, k) ==
    IF k = 0 \/ parent[n] = NoNode THEN {}
    ELSE {parent[n]} \cup Ancestors(parent[n], k - 1)

AncestorProperties ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node \ {initiator} :
          parent[n] # NoNode =>
             /\ R[n, parent[n]]
             /\ pc[parent[n]] \notin {"idle", "start"}
             /\ initiator \in Ancestors(n, Cardinality(Node))
             /\ n \notin Ancestors(n, Cardinality(Node))
    /\ \A n \in Node \ {initiator} : pc[n] # "idle" <=> parent[n] # NoNode
    /\ pc[initiator] = "done" =>
          \A n \in Node : pc[n] = "done"

=============================================================================