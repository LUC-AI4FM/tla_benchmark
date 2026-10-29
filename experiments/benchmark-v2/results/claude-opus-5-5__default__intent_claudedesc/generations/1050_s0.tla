------------------------------- MODULE Echo -------------------------------
(***************************************************************************)
(* The Echo algorithm on an undirected, connected network.                *)
(*                                                                         *)
(* A distinguished initiator sends an "explore" message to all its        *)
(* neighbors. When a non-initiator node receives its first message, it    *)
(* records the sender as its parent and forwards messages to all its      *)
(* other neighbors. Once a node has received a message from every         *)
(* neighbor, it sends an "echo" to its parent. The algorithm terminates   *)
(* when the initiator has received messages from all its neighbors.       *)
(* Exactly one message travels in each direction over each edge.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,       \* set of nodes in the network
    initiator,  \* the distinguished initiator node
    R           \* the communication relation, a set of pairs <<a, b>>

(***************************************************************************)
(* Helper definitions for topologies and graph properties.                *)
(***************************************************************************)
\* Fully connected (mesh) topology over a set of nodes, for model configs.
Mesh(S) == { e \in S \X S : e[1] # e[2] }

Nbrs(n) == { m \in Node : <<n, m>> \in R }

IsSymmetric(rel) == \A a, b \in Node : <<a, b>> \in rel => <<b, a>> \in rel

IsIrreflexive(rel) == \A a \in Node : <<a, a>> \notin rel

RECURSIVE ReachSet(_, _)
ReachSet(S, k) ==
    IF k = 0 THEN S
    ELSE ReachSet(S \cup { m \in Node : \E s \in S : <<s, m>> \in R }, k - 1)

IsConnected == \A n \in Node : ReachSet({n}, Cardinality(Node)) = Node

ASSUME NetworkAssumptions ==
    /\ IsFiniteSet(Node)
    /\ initiator \in Node
    /\ R \subseteq Node \X Node
    /\ IsSymmetric(R)
    /\ IsIrreflexive(R)
    /\ IsConnected

(***************************************************************************)
(* State                                                                   *)
(***************************************************************************)
VARIABLES
    active,   \* active[n]: n has been reached (started or received 1st msg)
    parent,   \* parent[n]: node from which n received its first message
    rcvd,     \* rcvd[n]: set of neighbors from which n has received a msg
    msgs,     \* set of in-transit messages <<from, to>>
    done,     \* done[n]: n has finished (echoed to parent / initiator decided)
    visits    \* visits[n]: number of times n was reached in forward phase

vars == << active, parent, rcvd, msgs, done, visits >>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ parent \in [Node -> Node]
    /\ rcvd   \in [Node -> SUBSET Node]
    /\ msgs   \subseteq R
    /\ done   \in [Node -> BOOLEAN]
    /\ visits \in [Node -> Nat]

(***************************************************************************)
(* Initial state: nothing has happened. parent[n] = n means "no parent"   *)
(* (well defined since R is irreflexive).                                  *)
(***************************************************************************)
Init ==
    /\ active = [n \in Node |-> FALSE]
    /\ parent = [n \in Node |-> n]
    /\ rcvd   = [n \in Node |-> {}]
    /\ msgs   = {}
    /\ done   = [n \in Node |-> FALSE]
    /\ visits = [n \in Node |-> 0]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
\* The initiator starts the algorithm by exploring all its neighbors.
Start ==
    /\ ~active[initiator]
    /\ active' = [active EXCEPT ![initiator] = TRUE]
    /\ visits' = [visits EXCEPT ![initiator] = @ + 1]
    /\ msgs'   = msgs \cup { <<initiator, m>> : m \in Nbrs(initiator) }
    /\ UNCHANGED << parent, rcvd, done >>

\* Node n receives a message from neighbor m.
Receive(n, m) ==
    /\ <<m, n>> \in msgs
    /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {m}]
    /\ IF ~active[n]
         THEN \* first message: adopt parent and forward to all other nbrs
              /\ n # initiator
              /\ active' = [active EXCEPT ![n] = TRUE]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ visits' = [visits EXCEPT ![n] = @ + 1]
              /\ msgs'   = (msgs \ {<<m, n>>})
                             \cup { <<n, k>> : k \in Nbrs(n) \ {m} }
         ELSE /\ msgs'   = msgs \ {<<m, n>>}
              /\ UNCHANGED << active, parent, visits >>
    /\ UNCHANGED done

\* Non-initiator n has heard from all neighbors: echo to its parent.
Echo(n) ==
    /\ n # initiator
    /\ active[n]
    /\ ~done[n]
    /\ rcvd[n] = Nbrs(n)
    /\ msgs' = msgs \cup { <<n, parent[n]>> }
    /\ done' = [done EXCEPT ![n] = TRUE]
    /\ UNCHANGED << active, parent, rcvd, visits >>

\* The initiator has heard from all neighbors: the algorithm terminates.
Decide ==
    /\ active[initiator]
    /\ ~done[initiator]
    /\ rcvd[initiator] = Nbrs(initiator)
    /\ done' = [done EXCEPT ![initiator] = TRUE]
    /\ UNCHANGED << active, parent, rcvd, msgs, visits >>

\* Stuttering after termination (avoids reporting deadlock).
Terminated ==
    /\ done[initiator]
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ \E n \in Node, m \in Node : Receive(n, m)
    \/ \E n \in Node : Echo(n)
    \/ Decide
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* Each node is reached at most once in the forward propagation phase.
VisitedAtMostOnce == \A n \in Node : visits[n] <= 1

\* Messages only travel along network edges.
MsgsOnEdges == msgs \subseteq R

\* A node only finishes after hearing from all its neighbors.
DoneImpliesAllReceived ==
    \A n \in Node : done[n] => (active[n] /\ rcvd[n] = Nbrs(n))

\* Parents of reached non-initiator nodes are neighbors that are active.
ParentIsNeighbor ==
    \A n \in Node \ {initiator} :
        active[n] => (parent[n] \in Nbrs(n) /\ active[parent[n]])

\* Proper acknowledgment: the initiator declares completion only after
\* every node has been reached exactly once and finished locally.
ProperAcknowledgment ==
    done[initiator] =>
        /\ \A n \in Node : active[n] /\ done[n] /\ visits[n] = 1
        /\ msgs = {}

Inv ==
    /\ TypeOK
    /\ VisitedAtMostOnce
    /\ MsgsOnEdges
    /\ DoneImpliesAllReceived
    /\ ParentIsNeighbor
    /\ ProperAcknowledgment

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* The algorithm eventually terminates at the initiator.
Termination == <>(done[initiator])

\* Complete coverage: every node is eventually reached exactly once.
CompleteCoverage == <>[](\A n \in Node : active[n] /\ visits[n] = 1)

\* Once terminated, all nodes have participated.
TerminationKnowsAll ==
    <>(done[initiator] /\ \A n \in Node : done[n])

THEOREM Spec => []Inv
THEOREM Spec => Termination /\ CompleteCoverage /\ TerminationKnowsAll
=============================================================================