------------------------------ MODULE EchoSpanningTree ------------------------------
(***************************************************************************)
(* Echo algorithm for constructing a spanning tree of an undirected,      *)
(* connected graph.  A designated initiator floods exploration messages   *)
(* ("m1") through the graph.  A non-initiator adopts the sender of the    *)
(* first m1 message it receives as its parent and forwards m1 to all its  *)
(* other neighbors.  Once a node has received one message from each of    *)
(* its neighbors, a non-initiator sends an acknowledgment ("m2") to its   *)
(* parent, which records the sender as a child.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node,        \* set of nodes
          initiator,   \* the distinguished root node
          R            \* neighborhood relation, a subset of Node \X Node

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : <<n, m>> \in R }

(***************************************************************************)
(* Assumptions about the graph.                                           *)
(***************************************************************************)
IsIrreflexive == \A n \in Node : <<n, n>> \notin R

IsSymmetric == \A m, n \in Node : <<m, n>> \in R <=> <<n, m>> \in R

IsConnected ==
    \A m, n \in Node :
        \E k \in 0 .. (Cardinality(Node) - 1) :
            \E p \in [0 .. k -> Node] :
                /\ p[0] = m
                /\ p[k] = n
                /\ \A i \in 0 .. (k - 1) : <<p[i], p[i + 1]>> \in R

ASSUME
    /\ IsFiniteSet(Node)
    /\ initiator \in Node
    /\ R \subseteq Node \X Node
    /\ IsIrreflexive
    /\ IsSymmetric
    /\ IsConnected

Msg == [kind : {"m1", "m2"}, sndr : Node]

VARIABLES
    inbox,     \* inbox[n] : set of messages pending at node n
    parent,    \* parent[n] : parent of node n, or NoNode
    children,  \* children[n] : set of nodes that acknowledged n as parent
    rcvd,      \* rcvd[n] : number of messages node n has received
    pc         \* control state of each node

vars == <<inbox, parent, children, rcvd, pc>>

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init ==
    /\ inbox    = [n \in Node |-> {}]
    /\ parent   = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ rcvd     = [n \in Node |-> 0]
    /\ pc       = [n \in Node |-> IF n = initiator THEN "start" ELSE "loop"]

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)

\* The initiator sends exploration messages to all its neighbors.
Start(n) ==
    /\ pc[n] = "start"
    /\ n = initiator
    /\ inbox' = [m \in Node |->
                    IF m \in neighbors(n)
                    THEN inbox[m] \cup {[kind |-> "m1", sndr |-> n]}
                    ELSE inbox[m]]
    /\ pc' = [pc EXCEPT ![n] = "loop"]
    /\ UNCHANGED <<parent, children, rcvd>>

\* Node n receives some message from its inbox (nondeterministic choice).
Receive(n) ==
    /\ pc[n] = "loop"
    /\ rcvd[n] < Cardinality(neighbors(n))
    /\ \E msg \in inbox[n] :
         /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
         /\ IF msg.kind = "m1"
            THEN IF n # initiator /\ parent[n] = NoNode
                 THEN \* first exploration message: adopt sender as parent
                      \* and forward exploration to the remaining neighbors
                      LET targets == neighbors(n) \ {msg.sndr}
                      IN  /\ parent' = [parent EXCEPT ![n] = msg.sndr]
                          /\ inbox' = [m \in Node |->
                                         IF m = n
                                         THEN inbox[n] \ {msg}
                                         ELSE IF m \in targets
                                              THEN inbox[m] \cup {[kind |-> "m1", sndr |-> n]}
                                              ELSE inbox[m]]
                          /\ UNCHANGED children
                 ELSE \* subsequent exploration message: just count it
                      /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg}]
                      /\ UNCHANGED <<parent, children>>
            ELSE \* acknowledgment: sender is a child
                 /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg}]
                 /\ children' = [children EXCEPT ![n] = @ \cup {msg.sndr}]
                 /\ UNCHANGED parent
    /\ UNCHANGED pc

\* Node n has heard from all neighbors; a non-initiator acknowledges its parent.
Finish(n) ==
    /\ pc[n] = "loop"
    /\ rcvd[n] = Cardinality(neighbors(n))
    /\ IF n # initiator
       THEN inbox' = [inbox EXCEPT ![parent[n]] = @ \cup {[kind |-> "m2", sndr |-> n]}]
       ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![n] = "done"]
    /\ UNCHANGED <<parent, children, rcvd>>

Proc(n) == Start(n) \/ Receive(n) \/ Finish(n)

Terminated == \A n \in Node : pc[n] = "done"

\* Allow stuttering once terminated (avoid spurious deadlock).
Terminating == Terminated /\ UNCHANGED vars

Next == (\E n \in Node : Proc(n)) \/ Terminating

Fairness == \A n \in Node : WF_vars(Proc(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                             *)
(***************************************************************************)

\* Type safety
TypeOK ==
    /\ inbox \in [Node -> SUBSET Msg]
    /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> 0 .. Cardinality(Node)]
    /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))
    /\ pc \in [Node -> {"start", "loop", "done"}]

\* Termination: all nodes eventually complete
Termination == <>Terminated

\* Valid parent assignment
ParentNeighbor ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node : parent[n] = NoNode \/ parent[n] \in neighbors(n)
    /\ Terminated => \A n \in Node \ {initiator} : parent[n] \in neighbors(n)

\* Consistent parent-child relationships
ChildrenSound ==
    \A n, m \in Node : m \in children[n] => parent[m] = n

ParentChildConsistent ==
    /\ ChildrenSound
    /\ Terminated =>
         \A n, m \in Node : m \in children[n] <=> parent[m] = n

\* Ancestors of n: nodes reachable by following parent pointers (>= 1 step)
Ancestors(n) ==
    LET N == Cardinality(Node)
        f[k \in 0 .. N] ==
            IF k = 0 THEN n
            ELSE IF f[k - 1] = NoNode THEN NoNode
                 ELSE parent[f[k - 1]]
    IN  { f[k] : k \in 1 .. N } \ {NoNode}

\* Spanning tree rooted at the initiator, acyclic ancestor relation
SpanningTree ==
    Terminated =>
        /\ \A n \in Node \ {initiator} : initiator \in Ancestors(n)
        /\ \A n \in Node : n \notin Ancestors(n)

THEOREM Spec => []TypeOK
THEOREM Spec => []ParentNeighbor
THEOREM Spec => []ParentChildConsistent
THEOREM Spec => []SpanningTree
THEOREM Spec => Termination
=====================================================================================