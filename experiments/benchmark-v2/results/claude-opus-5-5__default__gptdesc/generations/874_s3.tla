------------------------------ MODULE APSpanTree ------------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the SpanTree specification.               *)
(* It declares typed constants and variables, instantiates SpanTree, and   *)
(* supplies concrete constant values (via CInit) for a small three-node    *)
(* graph used by APSpanTree.cfg.                                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    Nodes,
    \* @type: Set(Set(Int));
    Edges,
    \* @type: Int;
    Root,
    \* @type: Int;
    MaxCardinality

VARIABLES
    \* @type: Int -> Int;
    mom,
    \* @type: Int -> Int;
    dist

ST == INSTANCE SpanTree

(***************************************************************************)
(* Concrete constant values for Apalache: a three-node line graph.         *)
(***************************************************************************)
CInit ==
    /\ Nodes = {1, 2, 3}
    /\ Edges = {{1, 2}, {2, 3}}
    /\ Root = 1
    /\ MaxCardinality = 3

(***************************************************************************)
(* Behavior is taken from SpanTree, not redefined locally.                 *)
(***************************************************************************)
TypeOK == ST!TypeOK

Init == ST!Init

Next == ST!Next

Spec == ST!Spec

=============================================================================