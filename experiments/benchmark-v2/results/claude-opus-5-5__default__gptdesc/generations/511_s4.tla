---------------------------- MODULE MCSession10set ----------------------------
EXTENDS Session10set, Naturals, FiniteSets

(***************************************************************************)
(* Model-checking wrapper for Session10set.                                *)
(* Assumes Session10set declares CONSTANTS Nodes, Edges, Root, the         *)
(* VARIABLES depth, parent, msgs, and defines Init, Next and Spec.         *)
(***************************************************************************)

\* Neighbors of a node in the (undirected) graph given by Edges
Neighbors(n) == { m \in Nodes : <<n, m>> \in Edges \/ <<m, n>> \in Edges }

\* Termination: all message queues are empty
Terminated == \A n \in Nodes : msgs[n] = {}

\* Type correctness of the imported state variables
TypeOK ==
  /\ depth  \in [Nodes -> Nat]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs   \in [Nodes -> SUBSET (Nodes \X Nat)]

\* Length of the parent path from n back to Root.
\* The fuel argument k bounds the recursion so it is well-founded even if
\* the parent pointers form a cycle.
RECURSIVE PathDepth(_, _)
PathDepth(n, k) ==
  IF n = Root THEN 0
  ELSE IF k = 0 THEN Cardinality(Nodes)
  ELSE 1 + PathDepth(parent[n], k - 1)

ParentDepth(n) == PathDepth(n, Cardinality(Nodes))

\* Set of nodes reachable from Root in at most k steps
RECURSIVE Reach(_)
Reach(k) ==
  IF k = 0 THEN {Root}
  ELSE Reach(k - 1) \cup UNION { Neighbors(m) : m \in Reach(k - 1) }

\* Graph distance of n from Root
Distance(n) ==
  IF \E k \in 0..Cardinality(Nodes) : n \in Reach(k)
    THEN CHOOSE k \in 0..Cardinality(Nodes) :
           /\ n \in Reach(k)
           /\ \A j \in 0..Cardinality(Nodes) : n \in Reach(j) => k <= j
    ELSE Cardinality(Nodes)

\* Correctness: upon termination, parent-path depth equals graph distance
Correct ==
  Terminated => \A n \in Nodes : ParentDepth(n) = Distance(n)

THEOREM Spec => [](TypeOK /\ Correct)
=============================================================================