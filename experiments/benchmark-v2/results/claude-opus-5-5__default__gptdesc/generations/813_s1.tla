---------------------------- MODULE APAParReach ----------------------------
(***************************************************************************)
(* Apalache-typed wrapper for the parallel reachability specification      *)
(* ParReach.  This module declares the constants and variables expected   *)
(* by ParReach, adds Apalache type annotations, and instantiates ParReach  *)
(* with direct substitutions.  It also supplies concrete constant values   *)
(* for nodes, successors, root and processes.                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    Nodes,
    \* @type: Int -> Set(Int);
    Succ,
    \* @type: Int;
    Root,
    \* @type: Set(Str);
    Procs

VARIABLES
    \* @type: Set(Int);
    marked,
    \* @type: Set(Int);
    vroot,
    \* @type: Str -> Str;
    pc,
    \* @type: Str -> Int;
    u,
    \* @type: Str -> Set(Int);
    toVroot

vars == <<marked, vroot, pc, u, toVroot>>

(***************************************************************************)
(* Instance of the underlying specification, substituting each parameter   *)
(* directly with the identically named, type-annotated declaration here.   *)
(***************************************************************************)
PR == INSTANCE ParReach
        WITH Nodes   <- Nodes,
             Succ    <- Succ,
             Root    <- Root,
             Procs   <- Procs,
             marked  <- marked,
             vroot   <- vroot,
             pc      <- pc,
             u       <- u,
             toVroot <- toVroot

(***************************************************************************)
(* Concrete constant values.                                               *)
(***************************************************************************)
\* @type: Set(Int);
NodesVal == 1..4

\* @type: Int -> Set(Int);
SuccVal == [n \in NodesVal |-> IF n = 1 THEN {2, 3}
                               ELSE IF n = 2 THEN {4}
                               ELSE IF n = 3 THEN {4}
                               ELSE {}]

\* @type: Int;
RootVal == 1

\* @type: Set(Str);
ProcsVal == {"p1", "p2"}

\* Apalache constant initialization predicate
ConstInit ==
    /\ Nodes = NodesVal
    /\ Succ  = SuccVal
    /\ Root  = RootVal
    /\ Procs = ProcsVal

(***************************************************************************)
(* The transition system, invariants and properties are those of ParReach; *)
(* they are re-exported here only by reference to the instance.            *)
(***************************************************************************)
Init == PR!Init

Next == PR!Next

Spec == PR!Spec

=============================================================================