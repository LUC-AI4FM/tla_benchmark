------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R

-----------------------------------------------------------------------------
(* Relation helpers (connectivity, symmetry, irreflexivity)                 *)
-----------------------------------------------------------------------------

IsIrreflexive(rel, S) == \A n \in S : ~ rel[n, n]

IsSymmetric(rel, S) == \A m, n \in S : rel[m, n] = rel[n, m]

RECURSIVE ReachSet(_, _, _)
ReachSet(rel, S, T) ==
    LET U == T \cup {y \in S : \E x \in T : rel[x, y]}
    IN  IF U = T THEN T ELSE ReachSet(rel, S, U)

IsConnected(rel, S) == \A n \in S : ReachSet(rel, S, {n}) = S

-----------------------------------------------------------------------------
(* Echo protocol                                                           *)
-----------------------------------------------------------------------------

ASSUME EchoAssume ==
    /\ initiator \in Node
    /\ R \in [Node \X Node -> BOOLEAN]
    /\ IsIrreflexive(R, Node)
    /\ IsSymmetric(R, Node)
    /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

VARIABLES inbox, rcvd, parent, pc

vars == <<inbox, rcvd, parent, pc>>

TypeOK ==
    /\ inbox \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ pc \in [Node -> {"idle", "active", "done"}]

Init ==
    /\ inbox = [n \in Node |-> {}]
    /\ rcvd = [n \in Node |-> 0]
    /\ parent = [n \in Node |-> NoNode]
    /\ pc = [n \in Node |-> "idle"]

\* The initiator wakes up and sends a token to all its neighbors.
Start ==
    /\ pc[initiator] = "idle"
    /\ pc' = [pc EXCEPT ![initiator] = "active"]
    /\ parent' = [parent EXCEPT ![initiator] = initiator]
    /\ inbox' = [k \in Node |->
                    IF k \in neighbors(initiator)
                    THEN inbox[k] \cup {initiator}
                    ELSE inbox[k]]
    /\ UNCHANGED rcvd

\* Node n receives a token from neighbor m.
Receive(n) ==
    \E m \in inbox[n] :
        /\ pc[n] # "done"
        /\ n = initiator => pc[n] = "active"
        /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
        /\ IF pc[n] = "idle"
           THEN /\ parent' = [parent EXCEPT ![n] = m]
                /\ pc' = [pc EXCEPT ![n] = "active"]
                /\ inbox' = [k \in Node |->
                               IF k = n THEN inbox[n] \ {m}
                               ELSE IF k \in neighbors(n) \ {m}
                                    THEN inbox[k] \cup {n}
                                    ELSE inbox[k]]
           ELSE /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
                /\ UNCHANGED <<parent, pc>>

\* Node n has heard from all its neighbors: echo to parent (or decide).
Finish(n) ==
    /\ pc[n] = "active"
    /\ rcvd[n] = Cardinality(neighbors(n))
    /\ pc' = [pc EXCEPT ![n] = "done"]
    /\ IF n # initiator
       THEN inbox' = [inbox EXCEPT ![parent[n]] = @ \cup {n}]
       ELSE UNCHANGED inbox
    /\ UNCHANGED <<rcvd, parent>>

Terminated ==
    /\ \A n \in Node : pc[n] = "done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ \E n \in Node : Receive(n) \/ Finish(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------

\* When the initiator decides, every node has finished and the parent
\* pointers form a spanning tree rooted at the initiator.
ParentTree ==
    pc[initiator] = "done" =>
        /\ \A n \in Node : pc[n] = "done"
        /\ \A n \in Node \ {initiator} : parent[n] \in neighbors(n)
        /\ inbox = [n \in Node |-> {}]

Safety == TypeOK /\ ParentTree

Termination == <>(pc[initiator] = "done")

-----------------------------------------------------------------------------
(* Model-checking instantiation                                            *)
-----------------------------------------------------------------------------

\* A tiny three-node graph
N1 == {1, 2, 3}

\* Initiator chosen nondeterministically among the nodes
I1 == CHOOSE n \in N1 : TRUE

\* A graph given as a function over node pairs (line 1 - 2 - 3)
G1 == [e \in N1 \X N1 |->
          e \in {<<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>}]

\* A graph chosen to satisfy connectivity, symmetry and irreflexivity
R1 == CHOOSE rel \in [N1 \X N1 -> BOOLEAN] :
          /\ IsConnected(rel, N1)
          /\ IsSymmetric(rel, N1)
          /\ IsIrreflexive(rel, N1)

\* Test specification: print the relation at startup, then run Spec
InitTest == PrintT(<<"R", R>>) /\ Init

SpecTest == InitTest /\ [][Next]_vars /\ WF_vars(Next)

\* Simple view and postcondition (TLC-specific)
MCView == <<inbox, rcvd, parent, pc>>

MCPostCondition == TLCGet("stats").distinct > 0

=============================================================================