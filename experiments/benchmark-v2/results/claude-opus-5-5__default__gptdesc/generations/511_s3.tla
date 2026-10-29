---------------------------- MODULE MCSession10set ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the spanning-tree / BFS-depth algorithm      *)
(* defined in module Session10set.  The extended module supplies the       *)
(* constants (Nodes, Root, Nbrs), the state variables (depth, parent,      *)
(* msgs), and the actions Init, Next and the full specification Spec       *)
(* (including its fairness conditions).  This module adds the termination  *)
(* condition, a type invariant, and a correctness property relating the    *)
(* parent-path depth of every node to its graph distance from the root.    *)
(***************************************************************************)
EXTENDS Session10set, Naturals, FiniteSets, TLC

-----------------------------------------------------------------------------
(***************************************************************************)
(* Termination: every message queue is empty.                              *)
(***************************************************************************)
Terminated == \A n \in Nodes : msgs[n] = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness of the imported state variables.                       *)
(***************************************************************************)
TypeOK ==
    /\ depth  \in [Nodes -> Nat]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs   \in [Nodes -> SUBSET Nat]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Parent paths.  PathFrom(n, k) is the sequence of nodes obtained by      *)
(* following parent pointers from n, for at most k steps, stopping at the  *)
(* root.  Bounding by k guarantees termination even if the parent          *)
(* pointers temporarily form a cycle.                                      *)
(***************************************************************************)
RECURSIVE PathFrom(_, _)
PathFrom(n, k) ==
    IF n = Root \/ k = 0
      THEN <<n>>
      ELSE <<n>> \o PathFrom(parent[n], k - 1)

ParentPath(n) == PathFrom(n, Cardinality(Nodes))

(***************************************************************************)
(* Depth of a node along its parent path (number of edges to the root).    *)
(***************************************************************************)
RECURSIVE PathDepthB(_, _)
PathDepthB(n, k) ==
    IF n = Root \/ k = 0
      THEN 0
      ELSE 1 + PathDepthB(parent[n], k - 1)

PathDepth(n) == PathDepthB(n, Cardinality(Nodes))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Graph distance from the root.  Ball(k) is the set of nodes reachable    *)
(* from Root in at most k hops.                                            *)
(***************************************************************************)
RECURSIVE Ball(_)
Ball(k) ==
    IF k = 0
      THEN {Root}
      ELSE LET B == Ball(k - 1)
           IN  B \cup {m \in Nodes : \E x \in B : m \in Nbrs(x)}

Distance(n) ==
    CHOOSE k \in 0..Cardinality(Nodes) :
        /\ n \in Ball(k)
        /\ (k = 0 \/ n \notin Ball(k - 1))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness: once the system has terminated, the parent-path depth of   *)
(* every node equals its distance from the root.                           *)
(***************************************************************************)
Correct ==
    Terminated => \A n \in Nodes : PathDepth(n) = Distance(n)

(***************************************************************************)
(* Liveness: the algorithm eventually terminates (under the fairness       *)
(* conditions included in Spec of Session10set).                           *)
(***************************************************************************)
EventuallyTerminates == <>Terminated

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Correct)
THEOREM Spec => EventuallyTerminates
=============================================================================