---------------------------- MODULE APAParReach ----------------------------
(***************************************************************************)
(* Typed wrapper for the parallel reachability specification ParReach.     *)
(* It declares the constants and variables of ParReach with Apalache type  *)
(* annotations, instantiates ParReach with direct substitutions, and       *)
(* supplies concrete values for nodes, successors, root and processes.     *)
(* The algorithm itself (actions, properties) is defined in ParReach.      *)
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

vars == << marked, vroot, pc, u, toVroot >>

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
(* Concrete constant values (to be used e.g. via ConstInit or a config).   *)
(***************************************************************************)
\* @type: Set(Int);
NodesVal == 1..5

\* @type: Int -> Set(Int);
SuccVal == [n \in NodesVal |->
              IF n = 1 THEN {2, 3}
              ELSE IF n = 2 THEN {4}
              ELSE IF n = 3 THEN {4, 5}
              ELSE IF n = 4 THEN {1}
              ELSE {}]

\* @type: Int;
RootVal == 1

\* @type: Set(Str);
ProcsVal == {"p1", "p2", "p3"}

\* Apalache-style constant initialization
ConstInit ==
    /\ Nodes = NodesVal
    /\ Succ  = SuccVal
    /\ Root  = RootVal
    /\ Procs = ProcsVal

(***************************************************************************)
(* The behavior is entirely that of the instantiated ParReach module.      *)
(***************************************************************************)
Init == PR!Init

Next == PR!Next

Spec == PR!Spec

=============================================================================