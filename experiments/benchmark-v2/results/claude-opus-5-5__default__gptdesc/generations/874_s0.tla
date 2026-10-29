---------------------------- MODULE APSpanTree ----------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the SpanTree specification.              *)
(*                                                                         *)
(* This module only supplies type annotations for the constants and       *)
(* variables, and concrete constant values for a small three-node graph.  *)
(* It does not define the spanning-tree algorithm. The behavior (Init,     *)
(* Next, Spec), the invariants and the temporal properties all come from   *)
(* instantiating the module SpanTree. APSpanTree.cfg refers to the         *)
(* definitions below.                                                      *)
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
(* Concrete constant values for a small three-node graph.                 *)
(* APSpanTree.cfg substitutes these values with "Nodes <- ConstNodes",     *)
(* and likewise for the other constants.                                   *)
(***************************************************************************)
ConstNodes == {1, 2, 3}

ConstEdges == {{1, 2}, {1, 3}, {2, 3}}

ConstRoot == 1

ConstMaxCardinality == 3

(***************************************************************************)
(* Unnamed instantiation of SpanTree. Every identifier is substituted by   *)
(* the identically named constant or variable of this module. As a         *)
(* result, Init, Next, Spec and the properties of SpanTree are available   *)
(* here without being redefined.                                           *)
(***************************************************************************)
INSTANCE SpanTree

=============================================================================