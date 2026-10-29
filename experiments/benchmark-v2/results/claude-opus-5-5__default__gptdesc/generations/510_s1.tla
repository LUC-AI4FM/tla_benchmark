------------------------------ MODULE SpanningTreePaths ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Edges, root, MaxNodes

(***************************************************************************)
(* Graph operators                                                         *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

(* Declarative definition: the smallest set of nodes that contains S and  *)
(* is closed under taking neighbors.                                       *)
ReachableFrom(S) ==
  {n \in Nodes : \A R \in SUBSET Nodes :
                    (S \subseteq R /\ SetNbrs(R) \subseteq R) => n \in R}

(* Executable recursive reachability procedure.                           *)
RECURSIVE RF(_)
RF(R) == LET RS == R \cup SetNbrs(R)
         IN  IF RS = R THEN R ELSE RF(RS)

(***************************************************************************)
(* Assumptions                                                             *)
(***************************************************************************)
ASSUME EdgeAssump ==
  \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

ASSUME RootAssump == root \in Nodes

ASSUME MaxNodesAssump ==
  /\ MaxNodes \in Nat
  /\ IsFiniteSet(Nodes)
  /\ Cardinality(Nodes) <= MaxNodes

ASSUME ConnectedAssump == Nodes = ReachableFrom({root})

(* The recursive procedure RF computes the declarative ReachableFrom.     *)
THEOREM RFCorrect == \A S \in SUBSET Nodes : RF(S) = ReachableFrom(S)

(***************************************************************************)
(* Distances from root                                                     *)
(***************************************************************************)
Ball[k \in Nat] == IF k = 0 THEN {root}
                   ELSE Ball[k-1] \cup SetNbrs(Ball[k-1])

Dist(n) == CHOOSE k \in 0..MaxNodes :
             /\ n \in Ball[k]
             /\ (k = 0 \/ n \notin Ball[k-1])

(***************************************************************************)
(* Distributed message-passing algorithm                                   *)
(*   Each node process n keeps depth[n] and parent[n].  A message          *)
(*   <<m, d>> sent to n says that node m has a path to root of length d.   *)
(*   On receiving it, if d+1 improves depth[n], node n adopts m as its     *)
(*   parent and informs all its neighbors of its new depth.                *)
(***************************************************************************)
VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

Msgs == Nodes \X (0..MaxNodes)

TypeOK ==
  /\ depth \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs \in [Nodes -> SUBSET Msgs]

Init ==
  /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs = [n \in Nodes |-> IF n \in Nbrs(root) THEN {<<root, 0>>} ELSE {}]

Receive(self) ==
  /\ msgs[self] # {}
  /\ \E m \in msgs[self] :
       LET from == m[1]
           d    == m[2]
       IN  IF d + 1 < depth[self]
             THEN /\ depth' = [depth EXCEPT ![self] = d + 1]
                  /\ parent' = [parent EXCEPT ![self] = from]
                  /\ msgs' = [k \in Nodes |->
                               IF k = self
                                 THEN msgs[self] \ {m}
                               ELSE IF k \in Nbrs(self)
                                 THEN msgs[k] \cup {<<self, d + 1>>}
                               ELSE msgs[k]]
             ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
                  /\ UNCHANGED <<depth, parent>>

proc(self) == Receive(self)

Next == \E self \in Nodes : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(proc(self))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
RootInv == depth[root] = 0 /\ parent[root] = root

ParentInv ==
  \A n \in Nodes \ {root} :
     depth[n] < MaxNodes =>
        /\ parent[n] \in Nbrs(n)
        /\ depth[parent[n]] < depth[n]

DepthLowerBound == \A n \in Nodes : depth[n] >= Dist(n)

MsgInv ==
  \A n \in Nodes : \A m \in msgs[n] :
     /\ m[1] \in Nbrs(n)
     /\ depth[m[1]] <= m[2]

Inv == TypeOK /\ RootInv /\ ParentInv /\ DepthLowerBound /\ MsgInv

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
Terminated == \A n \in Nodes : msgs[n] = {}

Termination == <>[]Terminated

CorrectDepths ==
  \A n \in Nodes : depth[n] = Dist(n)

SpanningTree ==
  /\ CorrectDepths
  /\ \A n \in Nodes \ {root} :
        /\ parent[n] \in Nbrs(n)
        /\ depth[parent[n]] = depth[n] - 1

Liveness == <>[]SpanningTree

THEOREM Spec => []Inv
THEOREM Spec => Termination /\ Liveness
=====================================================================================