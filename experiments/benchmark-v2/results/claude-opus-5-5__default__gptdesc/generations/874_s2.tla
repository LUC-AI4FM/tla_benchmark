------------------------------- MODULE APSpanTree -------------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the SpanTree specification.               *)
(*                                                                         *)
(* This module only supplies type annotations for the constants and        *)
(* variables, together with concrete constant values for a small           *)
(* three-node graph. The spanning-tree algorithm itself, including Init,   *)
(* Next, Spec, the invariants and the temporal properties, is defined in   *)
(* module SpanTree and is brought into scope by the INSTANCE below.        *)
(* It is used together with APSpanTree.cfg.                                *)
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

(***************************************************************************)
(* Instantiate SpanTree with identically named constants and variables.    *)
(* This makes Init, Next, Spec and all of SpanTree's properties available  *)
(* here without redefining them.                                           *)
(***************************************************************************)
INSTANCE SpanTree

(***************************************************************************)
(* Concrete example values for a three-node graph.                         *)
(***************************************************************************)
ApaNodes == {1, 2, 3}

ApaEdges == { {1, 2}, {1, 3}, {2, 3} }

ApaRoot == 1

ApaMaxCardinality == 3

(***************************************************************************)
(* Constant initialization predicate for Apalache (--cinit=ConstInit).     *)
(***************************************************************************)
ConstInit ==
    /\ Nodes = ApaNodes
    /\ Edges = ApaEdges
    /\ Root = ApaRoot
    /\ MaxCardinality = ApaMaxCardinality

=============================================================================