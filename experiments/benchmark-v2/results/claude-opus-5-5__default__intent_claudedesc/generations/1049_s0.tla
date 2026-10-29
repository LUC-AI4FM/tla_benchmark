------------------------------- MODULE EchoSpanningTree -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node,       \* finite set of nodes
          initiator,  \* designated initiator (root of the spanning tree)
          R           \* neighbor relation (set of ordered pairs)

NoNode == CHOOSE x : x \notin Node

nbrs(n) == {m \in Node : <<n, m>> \in R}

RECURSIVE Reach(_, _)
Reach(S, k) == IF k = 0 THEN S
               ELSE Reach(S \cup {m \in Node : \E n \in S : <<n, m>> \in R}, k - 1)

ASSUME /\ IsFiniteSet(Node)
       /\ initiator \in Node
       /\ R \subseteq Node \X Node
       /\ \A n \in Node : <<n, n>> \notin R                         \* no self-loops
       /\ \A m, n \in Node : <<m, n>> \in R => <<n, m>> \in R      \* undirected
       /\ Reach({initiator}, Cardinality(Node)) = Node             \* connected

VARIABLES state,     \* "idle", "active", "done"
          parent,    \* parent[n] \in Node \cup {NoNode}
          children,  \* children[n] \subseteq Node
          rcvd,      \* rcvd[n]: neighbors from which n has received a message
          msgs       \* messages in transit

vars == <<state, parent, children, rcvd, msgs>>

MsgType == {"explore", "child"}
Message == [type : MsgType, from : Node, to : Node]

TypeOK ==
  /\ state \in [Node -> {"idle", "active", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> SUBSET Node]
  /\ msgs \subseteq Message

Init ==
  /\ state = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> {}]
  /\ msgs = {}

\* The initiator starts by sending an exploration message to all its neighbors
Start ==
  /\ state[initiator] = "idle"
  /\ state' = [state EXCEPT ![initiator] = "active"]
  /\ msgs' = msgs \cup {[type |-> "explore", from |-> initiator, to |-> m] : m \in nbrs(initiator)}
  /\ UNCHANGED <<parent, children, rcvd>>

\* A non-initiator receives its first message: adopt sender as parent, forward to others
ReceiveFirst(n) ==
  /\ n # initiator
  /\ state[n] = "idle"
  /\ \E msg \in msgs :
       /\ msg.to = n
       /\ msg.type = "explore"
       /\ parent' = [parent EXCEPT ![n] = msg.from]
       /\ rcvd' = [rcvd EXCEPT ![n] = {msg.from}]
       /\ state' = [state EXCEPT ![n] = "active"]
       /\ msgs' = (msgs \ {msg}) \cup
                  {[type |-> "explore", from |-> n, to |-> m] : m \in nbrs(n) \ {msg.from}}
       /\ UNCHANGED children

\* An active node receives a subsequent message from a neighbor
ReceiveOther(n) ==
  /\ state[n] = "active"
  /\ \E msg \in msgs :
       /\ msg.to = n
       /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {msg.from}]
       /\ children' = IF msg.type = "child"
                        THEN [children EXCEPT ![n] = @ \cup {msg.from}]
                        ELSE children
       /\ msgs' = msgs \ {msg}
       /\ UNCHANGED <<state, parent>>

Receive(n) == ReceiveFirst(n) \/ ReceiveOther(n)

\* A node that has heard from all neighbors completes;
\* a non-initiator confirms the child relationship to its parent
Finish(n) ==
  /\ state[n] = "active"
  /\ rcvd[n] = nbrs(n)
  /\ state' = [state EXCEPT ![n] = "done"]
  /\ msgs' = IF n = initiator
               THEN msgs
               ELSE msgs \cup {[type |-> "child", from |-> n, to |-> parent[n]]}
  /\ UNCHANGED <<parent, children, rcvd>>

Next ==
  \/ Start
  \/ \E n \in Node : Receive(n) \/ Finish(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Start)
  /\ \A n \in Node : WF_vars(Receive(n)) /\ WF_vars(Finish(n))

-----------------------------------------------------------------------------
\* Derived notions

AllDone == \A n \in Node : state[n] = "done"

RECURSIVE Anc(_, _)
Anc(n, k) == IF k = 0 \/ parent[n] = NoNode THEN {}
             ELSE {parent[n]} \cup Anc(parent[n], k - 1)

Ancestors(n) == Anc(n, Cardinality(Node))

-----------------------------------------------------------------------------
\* Safety properties

\* Initiator never has a parent
InitiatorNoParent == parent[initiator] = NoNode

\* Every activated non-initiator has a parent that is a neighbor;
\* upon completion, every non-initiator has exactly one (neighbor) parent
ValidParent ==
  /\ \A n \in Node \ {initiator} :
        state[n] # "idle" => parent[n] \in nbrs(n)
  /\ AllDone => \A n \in Node \ {initiator} : parent[n] \in nbrs(n)

\* Children always consider the node their parent; upon completion the converse holds
ConsistentParentChild ==
  /\ \A m, n \in Node : n \in children[m] => parent[n] = m
  /\ AllDone => \A m, n \in Node : parent[n] = m => n \in children[m]

\* Upon termination, parent relationships form a spanning tree rooted at the initiator
SpanningTree ==
  AllDone =>
    \A n \in Node \ {initiator} :
       /\ initiator \in Ancestors(n)
       /\ n \notin Ancestors(n)

\* Each node has received at most one message from each neighbor
RcvdFromNeighbors == \A n \in Node : rcvd[n] \subseteq nbrs(n)

Safety ==
  /\ TypeOK
  /\ InitiatorNoParent
  /\ ValidParent
  /\ ConsistentParentChild
  /\ SpanningTree
  /\ RcvdFromNeighbors

-----------------------------------------------------------------------------
\* Liveness

Termination == <>AllDone

THEOREM Spec => []Safety
THEOREM Spec => Termination
=============================================================================