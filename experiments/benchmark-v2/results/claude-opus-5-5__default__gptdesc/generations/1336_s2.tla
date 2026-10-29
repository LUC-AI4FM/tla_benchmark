------------------------------- MODULE MCEcho -------------------------------
(***************************************************************************)
(* A tiny, fully connected, undirected graph with three nodes "a", "b",   *)
(* and "c", used to model check the Echo algorithm.  The module shows      *)
(* several ways of defining the node set and the edge relation, and        *)
(* includes the Echo algorithm itself, a test specification, invariants,   *)
(* liveness properties, and a postcondition for TLC.  It is meant for      *)
(* model checking and demonstration, not for generality.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Operators on binary relations, represented as Boolean-valued functions *)
(* over S \X S.                                                            *)
(***************************************************************************)
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

ReachableFrom(rel, S, m) ==
    LET reach[k \in Nat] ==
          IF k = 0 THEN {m}
          ELSE reach[k-1] \cup {y \in S : \E x \in reach[k-1] : rel[x, y]}
    IN  reach[Cardinality(S)]

IsConnected(rel, S) == \A m, n \in S : n \in ReachableFrom(rel, S, m)

(***************************************************************************)
(* Alternative definitions of the set of nodes.                           *)
(***************************************************************************)
NodesExplicit == {"a", "b", "c"}

NodesByDomain == DOMAIN [a |-> 1, b |-> 2, c |-> 3]

(***************************************************************************)
(* Alternative definitions of the edge relation.                          *)
(***************************************************************************)
\* Explicit fully connected, irreflexive relation.
RExplicit == [x \in NodesExplicit, y \in NodesExplicit |-> x # y]

\* Relation defined as a function over the domain-based node set.
RByDomain == [e \in NodesByDomain \X NodesByDomain |-> e[1] # e[2]]

\* Any relation that is connected, symmetric, and irreflexive.
RChoose ==
    CHOOSE r \in [NodesExplicit \X NodesExplicit -> BOOLEAN] :
        /\ IsConnected(r, NodesExplicit)
        /\ IsSymmetric(r, NodesExplicit)
        /\ IsIrreflexive(r, NodesExplicit)

(***************************************************************************)
(* The configuration used for model checking.                             *)
(***************************************************************************)
Nodes     == NodesExplicit
initiator == "a"
R         == RExplicit

ASSUME /\ NodesExplicit = NodesByDomain
       /\ initiator \in Nodes
       /\ R \in [Nodes \X Nodes -> BOOLEAN]
       /\ IsIrreflexive(R, Nodes)
       /\ IsSymmetric(R, Nodes)
       /\ IsConnected(R, Nodes)

NoNode == "none"

neighbors(n) == {m \in Nodes : R[m, n]}

Message == [kind : {"m", "c"}, sndr : Nodes]

(***************************************************************************)
(* The Echo algorithm.                                                     *)
(***************************************************************************)
VARIABLES inbox, parent, children, rcvd, pc

vars == <<inbox, parent, children, rcvd, pc>>

Init ==
    /\ inbox    = [n \in Nodes |-> {}]
    /\ parent   = [n \in Nodes |-> NoNode]
    /\ children = [n \in Nodes |-> {}]
    /\ rcvd     = [n \in Nodes |-> 0]
    /\ pc       = [n \in Nodes |-> "n0"]

\* Initiator multicasts an explore message to all neighbors.
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF self = initiator
         THEN /\ inbox' = [m \in Nodes |->
                             IF m \in neighbors(self)
                               THEN inbox[m] \cup {[kind |-> "m", sndr |-> self]}
                               ELSE inbox[m]]
              /\ parent' = [parent EXCEPT ![self] = self]
         ELSE UNCHANGED <<inbox, parent>>
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED <<children, rcvd>>

\* Receive a message from a neighbor.
n1(self) ==
    /\ pc[self] = "n1"
    /\ rcvd[self] < Cardinality(neighbors(self))
    /\ \E msg \in inbox[self] :
         LET newInbox == [inbox EXCEPT ![self] = @ \ {msg}]
         IN  /\ IF msg.kind = "m" /\ rcvd[self] = 0 /\ self # initiator
                  THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                       /\ inbox' = [m \in Nodes |->
                                      IF m \in neighbors(self) \ {msg.sndr}
                                        THEN newInbox[m] \cup {[kind |-> "m", sndr |-> self]}
                                        ELSE newInbox[m]]
                       /\ UNCHANGED children
                  ELSE IF msg.kind = "c"
                         THEN /\ children' = [children EXCEPT ![self] = @ \cup {msg.sndr}]
                              /\ inbox' = newInbox
                              /\ UNCHANGED parent
                         ELSE /\ inbox' = newInbox
                              /\ UNCHANGED <<parent, children>>
             /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
    /\ UNCHANGED pc

\* All neighbors heard from: echo back to parent and terminate.
n2(self) ==
    /\ pc[self] = "n1"
    /\ rcvd[self] = Cardinality(neighbors(self))
    /\ IF self # initiator
         THEN inbox' = [inbox EXCEPT ![parent[self]] =
                          @ \cup {[kind |-> "c", sndr |-> self]}]
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<parent, children, rcvd>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating ==
    /\ \A n \in Nodes : pc[n] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Nodes : node(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Test specification: print the chosen relation and run Echo's Spec.     *)
(***************************************************************************)
TestSpec == PrintT(RChoose) /\ Spec

(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
TypeOK ==
    /\ inbox    \in [Nodes -> SUBSET Message]
    /\ parent   \in [Nodes -> Nodes \cup {NoNode}]
    /\ children \in [Nodes -> SUBSET Nodes]
    /\ rcvd     \in [Nodes -> 0 .. Cardinality(Nodes)]
    /\ pc       \in [Nodes -> {"n0", "n1", "Done"}]

ParentsAreNeighbors ==
    \A n \in Nodes \ {initiator} :
        parent[n] # NoNode => parent[n] \in neighbors(n)

ChildrenAreNeighbors ==
    \A n \in Nodes : children[n] \subseteq neighbors(n)

ParentRel == [x \in Nodes, y \in Nodes |-> x # y /\ parent[x] = y]

\* Upon termination, parent edges form a spanning tree rooted at initiator.
PostCondition ==
    (\A n \in Nodes : pc[n] = "Done") =>
        /\ \A n \in Nodes : inbox[n] = {}
        /\ parent[initiator] = initiator
        /\ \A n \in Nodes \ {initiator} :
              /\ parent[n] \in neighbors(n)
              /\ n \in children[parent[n]]
              /\ initiator \in ReachableFrom(ParentRel, Nodes, n)
        /\ \A n \in Nodes : children[n] = {m \in Nodes \ {initiator} : parent[m] = n}

\* Postcondition for TLC, checked on terminal states.
PostConditionTLC == PostCondition

(***************************************************************************)
(* Liveness.                                                               *)
(***************************************************************************)
Termination == <>(\A n \in Nodes : pc[n] = "Done")

=============================================================================