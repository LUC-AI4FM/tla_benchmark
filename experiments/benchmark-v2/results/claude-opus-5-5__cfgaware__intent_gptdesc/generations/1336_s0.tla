------------------------------- MODULE Echo -------------------------------
(***************************************************************************)
(* Echo (flood / echo) algorithm on a reliable, undirected, connected      *)
(* network.  The initiator floods a token to all nodes; every node records *)
(* the neighbor from which it first received the token as its parent,      *)
(* forwards the token to all other neighbors exactly once, and once it has *)
(* heard from all its neighbors it sends a single echo to its parent.  The *)
(* initiator terminates when it has heard from all its neighbors.          *)
(* Network size and topology are parameters (Node, initiator, R).          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,       \* set of nodes
          initiator,  \* the initiating node
          R           \* neighborhood relation: [Node \X Node -> BOOLEAN]

(***************************************************************************)
(* Small test instance (3 nodes, line topology 1 - 2 - 3).                 *)
(***************************************************************************)
N1 == {1, 2, 3}
I1 == 1
R1 == [e \in N1 \X N1 |->
         \/ e = <<1, 2>> \/ e = <<2, 1>>
         \/ e = <<2, 3>> \/ e = <<3, 2>>]

NoNode == CHOOSE x : x \notin Node

neighbors(n) == {m \in Node : R[m, n]}

RECURSIVE Reach(_)
Reach(S) == LET T == S \cup {m \in Node : \E s \in S : R[s, m]}
            IN  IF T = S THEN S ELSE Reach(T)

IsIrreflexive == \A n \in Node : ~ R[n, n]
IsSymmetric   == \A m, n \in Node : R[m, n] = R[n, m]
IsConnected   == Reach({initiator}) = Node

ASSUME EchoAssumptions ==
          /\ IsFiniteSet(Node)
          /\ Node # {}
          /\ initiator \in Node
          /\ R \in [Node \X Node -> BOOLEAN]
          /\ IsIrreflexive
          /\ IsSymmetric
          /\ IsConnected

VARIABLES inbox,     \* inbox[n]: set of nodes whose message to n is in transit
          parent,    \* parent[n]: node from which n first received the token
          rcvd,      \* rcvd[n]: number of messages n has received
          status,    \* "idle", "active", "done"
          echoSent,  \* echoSent[n]: set of nodes to which n sent its echo
          fwd        \* fwd[n]: number of times n forwarded the broadcast

vars == <<inbox, parent, rcvd, status, echoSent, fwd>>

Send(box, from, targets) ==
   [m \in Node |-> IF m \in targets THEN box[m] \cup {from} ELSE box[m]]

TypeOK ==
   /\ inbox    \in [Node -> SUBSET Node]
   /\ parent   \in [Node -> Node \cup {NoNode}]
   /\ rcvd     \in [Node -> 0..Cardinality(Node)]
   /\ status   \in [Node -> {"idle", "active", "done"}]
   /\ echoSent \in [Node -> SUBSET Node]
   /\ fwd      \in [Node -> Nat]

Init ==
   /\ inbox    = [n \in Node |-> {}]
   /\ parent   = [n \in Node |-> NoNode]
   /\ rcvd     = [n \in Node |-> 0]
   /\ status   = [n \in Node |-> "idle"]
   /\ echoSent = [n \in Node |-> {}]
   /\ fwd      = [n \in Node |-> 0]

\* The initiator starts the broadcast.
Start ==
   /\ status[initiator] = "idle"
   /\ status' = [status EXCEPT ![initiator] = "active"]
   /\ inbox'  = Send(inbox, initiator, neighbors(initiator))
   /\ fwd'    = [fwd EXCEPT ![initiator] = @ + 1]
   /\ UNCHANGED <<parent, rcvd, echoSent>>

\* Node n receives a message from neighbor m.
Receive(n, m) ==
   /\ m \in inbox[n]
   /\ status[n] # "done"
   /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
   /\ IF status[n] = "idle"
        THEN \* first reception: record parent, forward to other neighbors
             /\ n # initiator
             /\ parent' = [parent EXCEPT ![n] = m]
             /\ status' = [status EXCEPT ![n] = "active"]
             /\ inbox'  = Send([inbox EXCEPT ![n] = @ \ {m}], n,
                               neighbors(n) \ {m})
             /\ fwd'    = [fwd EXCEPT ![n] = @ + 1]
        ELSE /\ inbox'  = [inbox EXCEPT ![n] = @ \ {m}]
             /\ UNCHANGED <<parent, status, fwd>>
   /\ UNCHANGED echoSent

\* Non-initiator n has heard from all neighbors: echo to parent.
Echo(n) ==
   /\ n # initiator
   /\ status[n] = "active"
   /\ rcvd[n] = Cardinality(neighbors(n))
   /\ status'   = [status EXCEPT ![n] = "done"]
   /\ inbox'    = Send(inbox, n, {parent[n]})
   /\ echoSent' = [echoSent EXCEPT ![n] = @ \cup {parent[n]}]
   /\ UNCHANGED <<parent, rcvd, fwd>>

\* Initiator has heard from all neighbors: terminate.
Finish ==
   /\ status[initiator] = "active"
   /\ rcvd[initiator] = Cardinality(neighbors(initiator))
   /\ status' = [status EXCEPT ![initiator] = "done"]
   /\ UNCHANGED <<inbox, parent, rcvd, echoSent, fwd>>

Terminated == status[initiator] = "done"

Next ==
   \/ Start
   \/ \E n \in Node : \E m \in Node : Receive(n, m)
   \/ \E n \in Node : Echo(n)
   \/ Finish
   \/ (Terminated /\ UNCHANGED vars)   \* avoid spurious deadlock

Spec     == Init /\ [][Next]_vars
TestSpec == Init /\ [][Next]_vars /\ WF_vars(Next)

View == vars

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
EchoOnce    == \A n \in Node : Cardinality(echoSent[n]) <= 1
EchoToParent == \A n \in Node : echoSent[n] \subseteq {parent[n]}
NoDuplicateForward == \A n \in Node : fwd[n] <= 1

RECURSIVE Up(_, _)
Up(n, k) == IF k = 0 \/ n = NoNode THEN n ELSE Up(parent[n], k - 1)

ReachesInitiator(n) ==
   \E k \in 0..Cardinality(Node) : Up(n, k) = initiator

\* Parent pointers form a tree rooted at the initiator (on reached nodes).
AncestorProperties ==
   /\ parent[initiator] = NoNode
   /\ \A n \in Node \ {initiator} :
         /\ (status[n] = "idle") <=> (parent[n] = NoNode)
         /\ parent[n] # NoNode =>
               /\ parent[n] \in neighbors(n)
               /\ status[parent[n]] # "idle"
               /\ ReachesInitiator(n)
   /\ EchoOnce
   /\ EchoToParent
   /\ NoDuplicateForward

\* Upon termination every node has seen the broadcast, sent exactly one
\* echo upstream, and the parent relation is a spanning tree.
PostCondition ==
   Terminated =>
      /\ \A n \in Node : status[n] = "done" /\ inbox[n] = {}
      /\ \A n \in Node \ {initiator} :
            /\ parent[n] \in neighbors(n)
            /\ echoSent[n] = {parent[n]}
            /\ ReachesInitiator(n)
      /\ parent[initiator] = NoNode
      /\ \A n \in Node : fwd[n] = 1

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>Terminated
Liveness    == <>[](Terminated /\ PostCondition)

THEOREM TestSpec => [](TypeOK /\ AncestorProperties /\ PostCondition)
THEOREM TestSpec => Termination
=============================================================================