---------------------------- MODULE MCSession10set ----------------------------
EXTENDS Session10set, Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Assumed to come from Session10set:                                      *)
(*   CONSTANTS Node, Root, Nbrs   (Nbrs \in [Node -> SUBSET Node])         *)
(*   VARIABLES depth, parent, msgs                                         *)
(*   Init, Next, Spec                                                      *)
(***************************************************************************)

MCVars == <<depth, parent, msgs>>

MCInit == Init

MCNext == Next

MCSpec == Spec

(***************************************************************************)
(* Termination: every message queue is empty.                              *)
(***************************************************************************)
Terminated == \A n \in Node : msgs[n] = {}

(***************************************************************************)
(* Type correctness of the imported state variables.                       *)
(***************************************************************************)
TypeOK ==
    /\ depth  \in [Node -> Nat]
    /\ parent \in [Node -> Node]
    /\ msgs   \in [Node -> SUBSET Nat]

(***************************************************************************)
(* Parent paths: the sequence of nodes obtained by following parent        *)
(* pointers from n until Root is reached (bounded to avoid divergence on   *)
(* cycles).                                                                *)
(***************************************************************************)
MaxLen == Cardinality(Node)

RECURSIVE ParentPathB(_, _)
ParentPathB(n, k) ==
    IF n = Root \/ k = 0
        THEN <<n>>
        ELSE <<n>> \o ParentPathB(parent[n], k - 1)

ParentPath(n) == ParentPathB(n, MaxLen)

(* Depth along the parent path: number of parent edges back to Root. *)
PathDepth(n) == Len(ParentPath(n)) - 1

(***************************************************************************)
(* Graph distance from Root, computed via breadth-first expansion.         *)
(***************************************************************************)
RECURSIVE Ball(_)
Ball(k) ==
    IF k = 0
        THEN {Root}
        ELSE Ball(k - 1) \cup UNION {Nbrs[m] : m \in Ball(k - 1)}

Distance(n) ==
    IF \E k \in 0..MaxLen : n \in Ball(k)
        THEN CHOOSE k \in 0..MaxLen :
                 /\ n \in Ball(k)
                 /\ \A j \in 0..MaxLen : j < k => n \notin Ball(j)
        ELSE MaxLen + 1

(***************************************************************************)
(* Correctness: upon termination, every node's parent-path depth equals    *)
(* its graph distance from the root.                                       *)
(***************************************************************************)
Correctness ==
    Terminated => \A n \in Node : PathDepth(n) = Distance(n)

THEOREM MCSpec => [](TypeOK /\ Correctness)
===============================================================================