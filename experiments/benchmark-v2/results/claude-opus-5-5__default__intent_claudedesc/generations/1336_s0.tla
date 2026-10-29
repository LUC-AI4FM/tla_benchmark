---------------------------- MODULE Echo ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node,       \* set of nodes in the network
          initiator,  \* the node that starts the algorithm
          R           \* the edge relation, a set of pairs of nodes

neighbors(n) == {m \in Node : <<m, n>> \in R}

\* Example topology for model checking: a fully connected mesh
FullMesh == {<<a, b>> \in Node \X Node : a # b}

\* Nodes reachable from a set S
RECURSIVE Reach(_)
Reach(S) == LET T == S \cup UNION {neighbors(x) : x \in S}
            IN  IF T = S THEN S ELSE Reach(T)

IsIrreflexive == \A n \in Node : <<n, n>> \notin R
IsSymmetric   == \A m, n \in Node : <<m, n>> \in R => <<n, m>> \in R
IsConnected   == \A n \in Node : Reach({n}) = Node

ASSUME /\ initiator \in Node
       /\ R \subseteq Node \X Node
       /\ IsIrreflexive
       /\ IsSymmetric
       /\ IsConnected

VARIABLES inbox,   \* inbox[n] : set of nodes whose message to n is in transit
          parent,  \* parent[n] : parent of n in spanning tree (n itself = none)
          rcvd,    \* rcvd[n] : number of messages n has received
          phase    \* phase[n] \in {"idle", "active", "done"}

vars == <<inbox, parent, rcvd, phase>>

TypeOK ==
    /\ inbox  \in [Node -> SUBSET Node]
    /\ parent \in [Node -> Node]
    /\ rcvd   \in [Node -> 0..Cardinality(Node)]
    /\ phase  \in [Node -> {"idle", "active", "done"}]

-----------------------------------------------------------------------------
Init ==
    /\ inbox  = [n \in Node |-> {}]
    /\ parent = [n \in Node |-> n]
    /\ rcvd   = [n \in Node |-> 0]
    /\ phase  = [n \in Node |-> "idle"]

\* The initiator starts the wave by sending to all its neighbors
Start ==
    /\ phase[initiator] = "idle"
    /\ phase' = [phase EXCEPT ![initiator] = "active"]
    /\ inbox' = [k \in Node |->
                   IF k \in neighbors(initiator) THEN inbox[k] \cup {initiator}
                   ELSE inbox[k]]
    /\ UNCHANGED <<parent, rcvd>>

\* Node n receives the message sent by m
Receive(n, m) ==
    /\ m \in inbox[n]
    /\ phase[n] # "done"
    /\ IF phase[n] = "idle"
       THEN \* first message: adopt sender as parent, forward to other neighbors
            /\ n # initiator
            /\ parent' = [parent EXCEPT ![n] = m]
            /\ rcvd'   = [rcvd EXCEPT ![n] = 1]
            /\ phase'  = [phase EXCEPT ![n] = "active"]
            /\ inbox'  = [k \in Node |->
                            IF k = n THEN inbox[n] \ {m}
                            ELSE IF k \in neighbors(n) \ {m}
                                 THEN inbox[k] \cup {n}
                                 ELSE inbox[k]]
       ELSE \* subsequent message: just count it
            /\ rcvd'  = [rcvd EXCEPT ![n] = @ + 1]
            /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
            /\ UNCHANGED <<parent, phase>>

\* Node n has heard from all neighbors: echo to parent (or terminate)
Finish(n) ==
    /\ phase[n] = "active"
    /\ rcvd[n] = Cardinality(neighbors(n))
    /\ phase' = [phase EXCEPT ![n] = "done"]
    /\ inbox' = IF n = initiator THEN inbox
                ELSE [inbox EXCEPT ![parent[n]] = @ \cup {n}]
    /\ UNCHANGED <<parent, rcvd>>

Next ==
    \/ Start
    \/ \E n \in Node, m \in Node : Receive(n, m)
    \/ \E n \in Node : Finish(n)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ WF_vars(Start)
    /\ \A n \in Node : WF_vars(Finish(n))
    /\ \A n, m \in Node : WF_vars(Receive(n, m))

-----------------------------------------------------------------------------
\* Helper: follow parent pointers up to k steps
RECURSIVE Up(_, _)
Up(n, k) == IF k = 0 \/ parent[n] = n THEN n ELSE Up(parent[n], k - 1)

Terminated == phase[initiator] = "done"

\* Safety properties

\* Parent pointers always go along edges to nodes that have joined the wave
ParentOK ==
    \A n \in Node :
        phase[n] # "idle" /\ n # initiator =>
            /\ parent[n] \in neighbors(n)
            /\ phase[parent[n]] # "idle"

\* The initiator never has a parent
InitiatorNoParent == parent[initiator] = initiator

\* When the initiator terminates, every node has participated and finished
CompleteCoverage ==
    Terminated => \A n \in Node : phase[n] = "done"

\* When the initiator terminates, no messages are in transit
NoMessagesAtEnd ==
    Terminated => \A n \in Node : inbox[n] = {}

\* At termination, parent pointers form a spanning tree rooted at the initiator
SpanningTree ==
    Terminated =>
        \A n \in Node :
            /\ n # initiator => parent[n] \in neighbors(n)
            /\ Up(n, Cardinality(Node)) = initiator

\* A node finishes only after receiving from all neighbors
FinishOK ==
    \A n \in Node : phase[n] = "done" => rcvd[n] = Cardinality(neighbors(n))

Invariants ==
    /\ TypeOK
    /\ ParentOK
    /\ InitiatorNoParent
    /\ CompleteCoverage
    /\ NoMessagesAtEnd
    /\ SpanningTree
    /\ FinishOK

\* Liveness properties

Termination == <>[]Terminated

EventualCoverage == \A n \in Node : <>(phase[n] = "done")

EventualSpanningTree ==
    <>[](\A n \in Node : Up(n, Cardinality(Node)) = initiator)

=============================================================================