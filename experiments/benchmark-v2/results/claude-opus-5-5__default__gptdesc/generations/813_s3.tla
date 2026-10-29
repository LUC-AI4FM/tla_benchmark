--------------------------- MODULE APAParReach ---------------------------
(***************************************************************************)
(* Typed wrapper around the ParReach specification. It provides Apalache  *)
(* type annotations for the constants and variables of ParReach and       *)
(* concrete constant values. The algorithm itself is defined in ParReach. *)
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

(***************************************************************************)
(* Concrete values for the constants.                                     *)
(***************************************************************************)
NodesVal == 1..5

SuccVal == [n \in NodesVal |-> IF n < 5 THEN {n + 1} ELSE {1}]

RootVal == 1

ProcsVal == {"p1", "p2", "p3"}

\* Apalache constant initialization predicate
ConstInit ==
    /\ Nodes = NodesVal
    /\ Succ = SuccVal
    /\ Root = RootVal
    /\ Procs = ProcsVal

(***************************************************************************)
(* Instance of the underlying specification, with direct substitutions.   *)
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

Init == PR!Init

Next == PR!Next

Spec == PR!Spec

=============================================================================