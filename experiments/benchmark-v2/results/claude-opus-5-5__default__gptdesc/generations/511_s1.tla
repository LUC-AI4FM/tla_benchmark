------------------------------ MODULE MCSession10set ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session10set system: a distributed      *)
(* spanning-tree / BFS-depth computation over an undirected graph.        *)
(* The underlying system (normally provided by EXTENDS Session10set) is   *)
(* reproduced here so that the module is self-contained and parses with   *)
(* SANY. The state variables are depth, parent and msgs.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes,   \* finite set of nodes
          Edges,   \* set of undirected edges, each a 2-element set {a, b}
          Root     \* distinguished root node

ASSUME /\ Root \in Nodes
       /\ IsFiniteSet(Nodes)
       /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

(* Sentinel for "infinite" depth: no simple path is this long. *)
INF == Cardinality(Nodes)

Nbrs(n) == {m \in Nodes : {n, m} \in Edges}

(***************************************************************************)
(* The system                                                             *)
(***************************************************************************)
Init ==
    /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE INF]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(Root) THEN {<<Root, 1>>} ELSE {}]

(* Node n consumes a message <<sender, d>>; if d improves its depth it    *)
(* adopts sender as parent and notifies its neighbours.                   *)
Receive(n) ==
    \E m \in msgs[n] :
        LET improve == m[2] < depth[n]
        IN  /\ depth'  = IF improve THEN [depth EXCEPT ![n] = m[2]] ELSE depth
            /\ parent' = IF improve THEN [parent EXCEPT ![n] = m[1]] ELSE parent
            /\ msgs'   = [k \in Nodes |->
                            IF k = n THEN msgs[n] \ {m}
                            ELSE IF improve /\ k \in Nbrs(n)
                                 THEN msgs[k] \cup {<<n, m[2] + 1>>}
                                 ELSE msgs[k]]

(***************************************************************************)
(* Termination: all message queues are empty                              *)
(***************************************************************************)
Terminated == \A n \in Nodes : msgs[n] = {}

Next ==
    \/ \E n \in Nodes : Receive(n)
    \/ (Terminated /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Receive(n))

(***************************************************************************)
(* Type correctness                                                       *)
(***************************************************************************)
TypeOK ==
    /\ depth  \in [Nodes -> 0..INF]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs   \in [Nodes -> SUBSET (Nodes \X (0..INF))]

(***************************************************************************)
(* Parent paths                                                           *)
(***************************************************************************)
(* The sequence of nodes obtained by following parent pointers from n     *)
(* towards the root, bounded by fuel to guarantee termination.            *)
RECURSIVE ParentPath(_, _)
ParentPath(n, fuel) ==
    IF n = Root \/ fuel = 0
    THEN <<n>>
    ELSE <<n>> \o ParentPath(parent[n], fuel - 1)

(* Length (in edges) of the parent path from n to the root; INF if the    *)
(* root is not reached within the bound.                                  *)
RECURSIVE PathDepthAux(_, _)
PathDepthAux(n, fuel) ==
    IF n = Root THEN 0
    ELSE IF fuel = 0 THEN INF
    ELSE LET d == PathDepthAux(parent[n], fuel - 1)
         IN  IF d = INF THEN INF ELSE d + 1

PathDepth(n) == PathDepthAux(n, INF)

(***************************************************************************)
(* Graph distance from the root                                           *)
(***************************************************************************)
RECURSIVE NodesWithin(_)
NodesWithin(k) ==
    IF k = 0
    THEN {Root}
    ELSE LET P == NodesWithin(k - 1)
         IN  P \cup UNION {Nbrs(p) : p \in P}

Distance(n) ==
    IF \E k \in 0..INF : n \in NodesWithin(k)
    THEN CHOOSE k \in 0..INF : /\ n \in NodesWithin(k)
                               /\ \A j \in 0..INF : n \in NodesWithin(j) => k <= j
    ELSE INF

(***************************************************************************)
(* Correctness: upon termination, parent-path depth equals distance       *)
(***************************************************************************)
Correct ==
    Terminated => \A n \in Nodes : PathDepth(n) = Distance(n)

(* Liveness: the algorithm eventually terminates. *)
EventuallyTerminates == <>Terminated

THEOREM Spec => [](TypeOK /\ Correct)
=============================================================================