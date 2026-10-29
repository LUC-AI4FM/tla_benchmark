------------------------------- MODULE Echo -------------------------------
(***************************************************************************)
(* The Echo algorithm builds a spanning tree of an undirected, connected   *)
(* graph, starting from a single initiator node.                           *)
(*                                                                         *)
(* --algorithm Echo {                                                      *)
(*   variable inbox = [n \in Node |-> {}];                                 *)
(*   macro multicast(snd, rcvs) {                                          *)
(*     inbox := [n \in Node |-> IF n \in rcvs                              *)
(*                 THEN inbox[n] \cup {[kind |-> "m", sndr |-> snd]}       *)
(*                 ELSE inbox[n]]                                          *)
(*   }                                                                     *)
(*   process (node \in Node)                                               *)
(*     variables parent = NoNode, children = {}, rcvd = 0,                 *)
(*               nbrs = neighbors(self);                                   *)
(*   {                                                                     *)
(*   n0: if (self = initiator) { multicast(self, nbrs) };                  *)
(*   n1: while (rcvd < Cardinality(nbrs)) {                                *)
(*         with (msg \in inbox[self]) {                                    *)
(*           rcvd := rcvd + 1;                                             *)
(*           if (self # initiator /\ rcvd = 1) {                           *)
(*             parent := msg.sndr;                                         *)
(*             multicast(self, nbrs \ {msg.sndr})                          *)
(*           } else if (msg.kind = "c") {                                  *)
(*             children := children \cup {msg.sndr}                        *)
(*           };                                                            *)
(*           inbox[self] := inbox[self] \ {msg}                            *)
(*         }                                                               *)
(*       };                                                                *)
(*   n2: if (self # initiator) {                                           *)
(*         inbox[parent] := inbox[parent] \cup                             *)
(*                          {[kind |-> "c", sndr |-> self]}                *)
(*       }                                                                 *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R

\* Nodes reachable from a set S of nodes in the graph R
RECURSIVE Reach(_)
Reach(S) ==
  LET T == S \cup { m \in Node : \E n \in S : R[n,m] }
  IN  IF T = S THEN S ELSE Reach(T)

IsIrreflexive == \A n \in Node : ~ R[n,n]
IsSymmetric   == \A m, n \in Node : R[m,n] = R[n,m]
IsConnected   == Reach({initiator}) = Node

ASSUME
  /\ initiator \in Node
  /\ R \in [Node \X Node -> BOOLEAN]
  /\ IsIrreflexive
  /\ IsSymmetric
  /\ IsConnected

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m,n] }

Msg == [kind : {"m", "c"}, sndr : Node]

VARIABLES inbox, pc, parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == Node

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ parent = [self \in Node |-> NoNode]
  /\ children = [self \in Node |-> {}]
  /\ rcvd = [self \in Node |-> 0]
  /\ nbrs = [self \in Node |-> neighbors(self)]
  /\ pc = [self \in ProcSet |-> "n0"]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN inbox' = [n \in Node |->
                        IF n \in nbrs[self]
                          THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                          ELSE inbox[n]]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(nbrs[self])
       THEN /\ \E msg \in inbox[self] :
                 /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                 /\ IF self # initiator /\ rcvd[self] + 1 = 1
                      THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                           /\ inbox' = [n \in Node |->
                                          IF n = self
                                            THEN inbox[n] \ {msg}
                                          ELSE IF n \in nbrs[self] \ {msg.sndr}
                                            THEN inbox[n] \cup
                                                   {[kind |-> "m", sndr |-> self]}
                                          ELSE inbox[n]]
                           /\ UNCHANGED children
                      ELSE /\ children' =
                                IF msg.kind = "c"
                                  THEN [children EXCEPT ![self] =
                                          children[self] \cup {msg.sndr}]
                                  ELSE children
                           /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                           /\ UNCHANGED parent
            /\ pc' = [pc EXCEPT ![self] = "n1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED << inbox, parent, children, rcvd >>
  /\ UNCHANGED nbrs

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
       THEN inbox' = [inbox EXCEPT ![parent[self]] =
                        inbox[parent[self]] \cup {[kind |-> "c", sndr |-> self]}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n)
  /\ \A n \in Node : rcvd[n] <= Cardinality(nbrs[n])

\* The initiator never gets a parent; parents and children are neighbors
ParentNeighbor ==
  /\ parent[initiator] = NoNode
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in nbrs[n]
  /\ \A n \in Node : children[n] \subseteq nbrs[n]

\* Consistency of parent / children relationships
ParentChild ==
  \A m, n \in Node :
     /\ n \in children[m] => m = parent[n]
     /\ (m = parent[n] /\ pc[m] = "Done") => n \in children[m]

\* Transitive closure of the parent relation
ParentRel == { <<n, parent[n]>> : n \in { x \in Node : parent[x] \in Node } }

RECURSIVE TC(_)
TC(Rel) ==
  LET Next2 == Rel \cup { <<a, c>> \in Node \X Node :
                            \E b \in Node : <<a, b>> \in Rel /\ <<b, c>> \in Rel }
  IN  IF Next2 = Rel THEN Rel ELSE TC(Next2)

\* The parent relation never contains a cycle
NoCycle == \A n \in Node : <<n, n>> \notin TC(ParentRel)

\* Upon termination, the parent relation forms a spanning tree rooted at
\* the initiator
SpanningTree ==
  (\A n \in Node : pc[n] = "Done") =>
     /\ \A n \in Node \ {initiator} : parent[n] \in Node
     /\ \A n \in Node \ {initiator} : <<n, initiator>> \in TC(ParentRel)

\* Eventually all nodes terminate
Termination == <>(\A n \in Node : pc[n] = "Done")

THEOREM Spec => [](TypeOK /\ ParentNeighbor /\ ParentChild /\ NoCycle /\ SpanningTree)
THEOREM Spec => Termination
=============================================================================