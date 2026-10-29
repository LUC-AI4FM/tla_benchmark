---------------------------- MODULE APAParReach ----------------------------
(***************************************************************************)
(* Typed wrapper around the ParReach specification. It declares the        *)
(* constants and variables used by ParReach with Apalache type             *)
(* annotations, and instantiates ParReach by substituting each parameter   *)
(* with the annotated name of the same name from this module. It also      *)
(* gives concrete values for nodes, successors, root and processes.        *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Set(Int);
    Nodes,
    \* @type: Set(<<Int, Int>>);
    SuccRelation,
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

\* Instance of the underlying specification, with direct substitutions.
R == INSTANCE ParReach
        WITH Nodes        <- Nodes,
             SuccRelation <- SuccRelation,
             Root         <- Root,
             Procs        <- Procs,
             marked       <- marked,
             vroot        <- vroot,
             pc           <- pc,
             u            <- u,
             toVroot      <- toVroot

\* Concrete values for the constants (e.g. for an Apalache ConstInit).
ConstNodes == 1..5

ConstSuccRelation ==
    {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>, <<4, 5>>, <<5, 1>>}

ConstRoot == 1

ConstProcs == {"p1", "p2", "p3"}

\* Constant initialization predicate for Apalache.
ConstInit ==
    /\ Nodes = ConstNodes
    /\ SuccRelation = ConstSuccRelation
    /\ Root = ConstRoot
    /\ Procs = ConstProcs

vars == <<marked, vroot, pc, u, toVroot>>

\* The transition system is taken entirely from ParReach.
Init == R!Init

Next == R!Next

Spec == Init /\ [][Next]_vars

=============================================================================