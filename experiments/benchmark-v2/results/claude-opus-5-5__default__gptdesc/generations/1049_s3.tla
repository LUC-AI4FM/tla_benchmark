--------------------------------- MODULE Echo ---------------------------------
(***************************************************************************)
(* The Echo algorithm for constructing a spanning tree in an undirected,   *)
(* connected graph, starting from a single initiator node.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, will be the root of the tree
          R          \* neighborhood relation, a Boolean function over Node \X Node

(***************************************************************************)
(* Properties of relations (defined locally to keep the module             *)
(* self-contained).                                                        *)
(***************************************************************************)
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]

IsSymmetric(rel, S) == \A x, y \in S : rel[x, y] <=> rel[y, x]

RECURSIVE ReachAux(_, _, _)
ReachAux(rel, S, reached) ==
    LET next == reached \cup {y \in S : \E x \in reached : rel[x, y]}
    IN  IF next = reached THEN reached ELSE ReachAux(rel, S, next)

ReachableFrom(rel, S, x) == ReachAux(rel, S, {x})

IsConnected(rel, S) == \A x \in S : ReachableFrom(rel, S, x) = S

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       \* No edge from a node to itself (no self-loops).
       /\ IsIrreflexive(R, Node)
       \* Undirected graph.
       /\ IsSymmetric(R, Node)
       \* The graph is connected (a spanning tree over all nodes exists).
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];

    macro send(dest, msg) {
        inbox[dest] := inbox[dest] \cup {msg};
    }

    macro multicast(dests, msg) {
        inbox := [n \in Node |-> IF n \in dests
                                 THEN inbox[n] \cup {msg}
                                 ELSE inbox[n]];
    }

    process (node \in Node)
      variables parent = NoNode,
                children = {},
                rcvd = 0,
                nbrs = neighbors(self);
    {
    n0: if (self = initiator) {
           \* initiator sends a first message to all its neighbors
           multicast(nbrs, [kind |-> "m", sndr |-> self]);
        } else {
           \* receive first message, which determines the parent
           with (msg \in inbox[self]) {
              parent := msg.sndr;
              rcvd := 1;
              nbrs := nbrs \ {msg.sndr};
              inbox := [n \in Node |->
                          IF n = self THEN inbox[self] \ {msg}
                          ELSE IF n \in nbrs \ {msg.sndr}
                               THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                               ELSE inbox[n]];
           }
        };
    n1: while (rcvd < Cardinality(neighbors(self))) {
           \* receive messages from all neighbors
           with (msg \in inbox[self]) {
              if (msg.kind = "c") {
                 children := children \cup {msg.sndr};
              };
              inbox[self] := inbox[self] \ {msg};
              rcvd := rcvd + 1;
           }
        };
        if (self # initiator) {
           \* echo back to the parent
           send(parent, [kind |-> "c", sndr |-> self]);
        };
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == Node

Init == /\ inbox = [n \in Node |-> {}]
        /\ parent = [self \in Node |-> NoNode]
        /\ children = [self \in Node |-> {}]
        /\ rcvd = [self \in Node |-> 0]
        /\ nbrs = [self \in Node |-> neighbors(self)]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF self = initiator
                  THEN /\ inbox' = [n \in Node |->
                                      IF n \in nbrs[self]
                                      THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                      ELSE inbox[n]]
                       /\ UNCHANGED << parent, rcvd, nbrs >>
                  ELSE /\ \E msg \in inbox[self]:
                            /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                            /\ rcvd' = [rcvd EXCEPT ![self] = 1]
                            /\ nbrs' = [nbrs EXCEPT ![self] = nbrs[self] \ {msg.sndr}]
                            /\ inbox' = [n \in Node |->
                                           IF n = self THEN inbox[self] \ {msg}
                                           ELSE IF n \in nbrs[self] \ {msg.sndr}
                                                THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                                ELSE inbox[n]]
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED children

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(neighbors(self))
                  THEN /\ \E msg \in inbox[self]:
                            /\ IF msg.kind = "c"
                                  THEN children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                  ELSE UNCHANGED children
                            /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                            /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ IF self # initiator
                             THEN inbox' = [inbox EXCEPT ![parent[self]] =
                                              inbox[parent[self]] \cup {[kind |-> "c", sndr |-> self]}]
                             ELSE UNCHANGED inbox
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << children, rcvd >>
            /\ UNCHANGED << parent, nbrs >>

node(self) == n0(self) \/ n1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

-------------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
Message == [kind : {"m", "c"}, sndr : Node]

TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]
    /\ \A n \in Node : nbrs[n] \subseteq neighbors(n)
    /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))
    /\ inbox \in [Node -> SUBSET Message]
    /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
    /\ pc \in [Node -> {"n0", "n1", "Done"}]

\* The initiator never has a parent.
InitiatorNoParent == parent[initiator] = NoNode

\* The parent of a node, if any, is one of its neighbors.
ParentIsNeighbor ==
    \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

\* Every child of a node has that node as its parent.
ParentChild ==
    \A m, n \in Node : n \in children[m] => m = parent[n]

\* Ancestors of a node following the parent chain.
RECURSIVE AncestorsAux(_, _)
AncestorsAux(n, visited) ==
    IF parent[n] = NoNode \/ parent[n] \in visited
    THEN visited
    ELSE AncestorsAux(parent[n], visited \cup {parent[n]})

Ancestors(n) == AncestorsAux(n, {})

AllDone == \A n \in Node : pc[n] = "Done"

\* At termination, every non-initiator node has a parent, the initiator is
\* an ancestor of every other node, and no node is its own ancestor.
AncestorProp ==
    AllDone =>
       /\ \A n \in Node \ {initiator} : parent[n] \in Node
       /\ \A n \in Node \ {initiator} : initiator \in Ancestors(n)
       /\ \A n \in Node : n \notin Ancestors(n)

\* At termination, the children relation is exactly the inverse of parent.
ChildrenAtTermination ==
    AllDone =>
       \A m, n \in Node : n \in children[m] <=> m = parent[n]

THEOREM Spec => [](TypeOK /\ InitiatorNoParent /\ ParentIsNeighbor
                   /\ ParentChild /\ AncestorProp /\ ChildrenAtTermination)
THEOREM Spec => Termination
===============================================================================