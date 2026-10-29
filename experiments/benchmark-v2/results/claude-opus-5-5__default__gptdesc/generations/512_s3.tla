---------------------------- MODULE PathsToRoot ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxNodes

(***************************************************************************)
(* Graph structure and recursive reachability definitions                  *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

\* ReachIn(k): set of nodes reachable from Root by a path of at most k edges
RECURSIVE ReachIn(_)
ReachIn(k) == IF k = 0
                THEN {Root}
                ELSE ReachIn(k - 1) \cup UNION {Nbrs(n) : n \in ReachIn(k - 1)}

\* IsPath(p): p is a sequence of nodes in which consecutive nodes are joined
\* by an edge
RECURSIVE IsPathFrom(_, _, _)
IsPathFrom(a, b, k) ==
    IF k = 0 THEN a = b
    ELSE \/ a = b
         \/ \E m \in Nbrs(a) : IsPathFrom(m, b, k - 1)

Reachable(n) == IsPathFrom(Root, n, MaxNodes)

ReachableSet == ReachIn(MaxNodes)

ASSUME EdgeAssump   == \A e \in Edges : /\ e \subseteq Nodes
                                        /\ Cardinality(e) = 2
ASSUME RootAssump   == Root \in Nodes
ASSUME MaxNodesAssump == /\ MaxNodes \in Nat
                         /\ IsFiniteSet(Nodes)
                         /\ Cardinality(Nodes) <= MaxNodes
ASSUME ConnectedAssump == /\ \A n \in Nodes : Reachable(n)
                          /\ ReachableSet = Nodes

\* Distance (number of edges on a shortest path) from Root to n
Dist(n) == CHOOSE k \in 0..MaxNodes :
               /\ n \in ReachIn(k)
               /\ (k = 0 \/ n \notin ReachIn(k - 1))

Infinity == MaxNodes   \* depth value meaning "no path found yet"

(***************************************************************************)
(* --algorithm PathsToRoot                                                 *)
(*   variables msgs  = [n \in Nodes |-> IF n \in Nbrs(Root)                *)
(*                                        THEN {<<Root, 0>>} ELSE {}],     *)
(*             depth = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity], *)
(*             parent = [n \in Nodes |-> n];                               *)
(*   fair process (node \in Nodes)                                         *)
(*   { a: while (TRUE) {                                                   *)
(*          await msgs[self] # {};                                         *)
(*          with (m \in msgs[self]) {                                      *)
(*            if (m[2] + 1 < depth[self]) {                                *)
(*              depth[self] := m[2] + 1 ; parent[self] := m[1] ;           *)
(*              msgs := [n \in Nodes |->                                   *)
(*                        IF n = self THEN msgs[self] \ {m}                *)
(*                        ELSE IF n \in Nbrs(self)                         *)
(*                               THEN msgs[n] \cup {<<self, m[2]+1>>}      *)
(*                               ELSE msgs[n]]                             *)
(*            } else { msgs[self] := msgs[self] \ {m} }                    *)
(*          } } }                                                          *)
(* end algorithm                                                           *)
(***************************************************************************)

VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == Nodes

Init == /\ msgs = [n \in Nodes |-> IF n \in Nbrs(Root)
                                      THEN {<<Root, 0>>} ELSE {}]
        /\ depth = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
        /\ parent = [n \in Nodes |-> n]

node(self) ==
    /\ msgs[self] # {}
    /\ \E m \in msgs[self] :
         IF m[2] + 1 < depth[self]
           THEN /\ depth' = [depth EXCEPT ![self] = m[2] + 1]
                /\ parent' = [parent EXCEPT ![self] = m[1]]
                /\ msgs' = [n \in Nodes |->
                              IF n = self THEN msgs[self] \ {m}
                              ELSE IF n \in Nbrs(self)
                                     THEN msgs[n] \cup {<<self, m[2] + 1>>}
                                     ELSE msgs[n]]
           ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
                /\ UNCHANGED << depth, parent >>

Next == \E self \in Nodes : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
    /\ msgs \in [Nodes -> SUBSET (Nodes \X (0..MaxNodes))]
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]

DepthBound == \A n \in Nodes : depth[n] >= Dist(n)

RootOK == depth[Root] = 0 /\ parent[Root] = Root

ParentOK ==
    \A n \in Nodes \ {Root} :
        depth[n] < Infinity =>
            /\ parent[n] \in Nbrs(n)
            /\ depth[parent[n]] < depth[n]

MsgOK ==
    \A n \in Nodes : \A m \in msgs[n] :
        /\ m[1] \in Nbrs(n)
        /\ depth[m[1]] <= m[2]

Inv == TypeOK /\ DepthBound /\ RootOK /\ ParentOK /\ MsgOK

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
DepthsCorrect == \A n \in Nodes : depth[n] = Dist(n)

ParentsCorrect ==
    \A n \in Nodes \ {Root} :
        /\ parent[n] \in Nbrs(n)
        /\ Dist(parent[n]) = Dist(n) - 1

Termination == <>[](\A n \in Nodes : msgs[n] = {})

Liveness == <>[](DepthsCorrect /\ ParentsCorrect)

THEOREM Spec => []Inv
THEOREM Spec => Liveness /\ Termination
=============================================================================