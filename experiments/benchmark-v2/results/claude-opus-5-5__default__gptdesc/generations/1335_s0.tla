--------------------------------- MODULE Echo ---------------------------------
(***************************************************************************)
(* The Echo algorithm builds a spanning tree of an undirected, connected   *)
(* graph, starting from a single initiator node. The initiator sends an    *)
(* explorer message "m" to all its neighbors. When a non-initiator         *)
(* receives its first message, it records the sender as its parent and     *)
(* forwards "m" to all its other neighbors. Once a node has heard from all *)
(* of its neighbors, it sends a "c" (child / echo) message to its parent.  *)
(* The algorithm ends when the initiator has heard from all its neighbors. *)
(*                                                                         *)
(* The PlusCal algorithm is kept below as a comment. The TLA+ part that    *)
(* follows is its translation, with explicit state variables and actions. *)
(*                                                                         *)
(* --algorithm Echo {                                                      *)
(*   variable inbox = [n \in Node |-> {}];                                 *)
(*   process (node \in Node)                                               *)
(*     variables parent = NoNode, children = {}, rcvd = 0; {               *)
(*   n0: if (self = initiator) {                                           *)
(*         inbox := multicast(inbox, self, neighbors(self), "m")           *)
(*       };                                                                *)
(*   n1: while (rcvd < Cardinality(neighbors(self))) {                     *)
(*         with (msg \in inbox[self],                                      *)
(*               net = [inbox EXCEPT ![self] = @ \ {msg}]) {               *)
(*           rcvd := rcvd + 1;                                             *)
(*           if (self # initiator /\ rcvd = 1) {                           *)
(*             assert msg.kind = "m";                                      *)
(*             parent := msg.sndr;                                         *)
(*             inbox := multicast(net, self,                               *)
(*                                neighbors(self) \ {msg.sndr}, "m")       *)
(*           } else if (msg.kind = "c") {                                  *)
(*             children := children \cup {msg.sndr};                       *)
(*             inbox := net                                                *)
(*           } else { inbox := net }                                       *)
(*         }                                                               *)
(*       };                                                                *)
(*   n2: if (self # initiator) {                                           *)
(*         inbox := send(inbox, self, parent, "c")                         *)
(*       }                                                                 *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node,       \* set of nodes
          initiator,  \* single initiator, root of the spanning tree
          R           \* neighborhood relation, a Boolean function over Node \X Node

-----------------------------------------------------------------------------
(* Properties of relations, defined locally *)

IsIrreflexive(rel, S) == \A n \in S : ~ rel[n, n]

IsSymmetric(rel, S) == \A m, n \in S : rel[m, n] = rel[n, m]

RECURSIVE ReachFrom(_, _, _)
ReachFrom(rel, X, S) ==
    LET Y == X \cup {n \in S : \E m \in X : rel[m, n]}
    IN  IF Y = X THEN X ELSE ReachFrom(rel, Y, S)

IsConnected(rel, S) == \A n \in S : ReachFrom(rel, {n}, S) = S

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)   \* no self loops
       /\ IsSymmetric(R, Node)     \* undirected graph
       /\ IsConnected(R, Node)     \* graph is connected

-----------------------------------------------------------------------------

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

Kinds == {"m", "c"}
Msg   == [kind : Kinds, sndr : Node]

send(box, i, j, k) ==
    [box EXCEPT ![j] = @ \cup {[kind |-> k, sndr |-> i]}]

multicast(box, i, js, k) ==
    [n \in Node |-> IF n \in js
                    THEN box[n] \cup {[kind |-> k, sndr |-> i]}
                    ELSE box[n]]

-----------------------------------------------------------------------------
VARIABLES inbox, pc, parent, children, rcvd

vars == << inbox, pc, parent, children, rcvd >>

ProcSet == Node

Init ==
    /\ inbox    = [n \in Node |-> {}]
    /\ parent   = [self \in Node |-> NoNode]
    /\ children = [self \in Node |-> {}]
    /\ rcvd     = [self \in Node |-> 0]
    /\ pc       = [self \in ProcSet |-> "n0"]

n0(self) ==
    /\ pc[self] = "n0"
    /\ IF self = initiator
         THEN inbox' = multicast(inbox, self, neighbors(self), "m")
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << parent, children, rcvd >>

n1(self) ==
    /\ pc[self] = "n1"
    /\ IF rcvd[self] < Cardinality(neighbors(self))
         THEN /\ \E msg \in inbox[self] :
                   LET net == [inbox EXCEPT ![self] = @ \ {msg}]
                   IN  /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
                       /\ IF self # initiator /\ rcvd'[self] = 1
                            THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                 /\ inbox' = multicast(net, self,
                                                neighbors(self) \ {msg.sndr}, "m")
                                 /\ UNCHANGED children
                            ELSE /\ IF msg.kind = "c"
                                      THEN children' = [children EXCEPT
                                                          ![self] = @ \cup {msg.sndr}]
                                      ELSE UNCHANGED children
                                 /\ inbox' = net
                                 /\ UNCHANGED parent
              /\ pc' = [pc EXCEPT ![self] = "n1"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
              /\ UNCHANGED << inbox, parent, children, rcvd >>

n2(self) ==
    /\ pc[self] = "n2"
    /\ IF self # initiator
         THEN inbox' = send(inbox, self, parent[self], "c")
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << parent, children, rcvd >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ inbox    \in [Node -> SUBSET Msg]
    /\ parent   \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd     \in [Node -> Nat]
    /\ pc       \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))

(* The initiator never has a parent; every parent is a neighbor. *)
ParentNeighbor ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

(* Children are consistent with parents; once a node is done, all its     *)
(* children have been registered.                                          *)
ParentChild ==
    \A m, n \in Node :
        /\ n \in children[m] => m = parent[n]
        /\ m = parent[n] /\ pc[m] = "Done" => n \in children[m]

(* Messages are only sent between neighbors. *)
MessagesFromNeighbors ==
    \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)

(* Following parent pointers from any node with a parent leads to the      *)
(* initiator: the parent relation is acyclic and rooted at the initiator.  *)
RECURSIVE PIter(_, _)
PIter(n, k) ==
    IF k = 0 THEN n
    ELSE IF n \in Node /\ parent[n] # NoNode THEN PIter(parent[n], k - 1)
    ELSE n

ReachesRoot(n) == \E k \in 0 .. Cardinality(Node) : PIter(n, k) = initiator

Acyclic ==
    \A n \in Node : parent[n] # NoNode => ReachesRoot(n)

(* A node that is done has heard from every neighbor. *)
DoneHeardAll ==
    \A n \in Node : pc[n] = "Done" => rcvd[n] = Cardinality(neighbors(n))

AllDone == \A n \in Node : pc[n] = "Done"

(* When the algorithm has terminated, the parent relation is a spanning    *)
(* tree containing all nodes, rooted at the initiator, and no messages     *)
(* remain in transit.                                                      *)
SpanningTree ==
    AllDone =>
        /\ \A n \in Node \ {initiator} : parent[n] \in neighbors(n)
        /\ \A n \in Node : ReachesRoot(n)
        /\ \A n \in Node : inbox[n] = {}

Inv ==
    /\ TypeOK
    /\ ParentNeighbor
    /\ ParentChild
    /\ MessagesFromNeighbors
    /\ Acyclic
    /\ DoneHeardAll
    /\ SpanningTree

-----------------------------------------------------------------------------
(* Liveness properties *)

Termination == <>AllDone

StableTermination == <>[]AllDone

InitiatorTerminates == <>(pc[initiator] = "Done")

=============================================================================