------------------------------- MODULE APSpanTree -------------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the SpanTree specification.               *)
(*                                                                         *)
(* This module adds Apalache type annotations to the constants and         *)
(* variables, and gives concrete constant values for a small three-node    *)
(* graph used by APSpanTree.cfg.                                           *)
(*                                                                         *)
(* It does not define the spanning-tree algorithm, its actions, or its     *)
(* temporal properties. The unnamed INSTANCE below imports all of those    *)
(* from SpanTree, including Init, Next, Spec, and the invariants and       *)
(* properties declared there. Because the instance is unnamed, they are    *)
(* used here under their original names and are not redefined locally.    *)
(***************************************************************************)
EXTENDS Integers

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
(* Import the behavior (Init, Next, Spec), the invariants, and the         *)
(* temporal properties from SpanTree. No substitution is needed because    *)
(* each constant and variable here has the same name as in SpanTree.       *)
(***************************************************************************)
INSTANCE SpanTree

(***************************************************************************)
(* Concrete constant values for a three-node graph with every pair of      *)
(* nodes connected and node 1 as the root.                                 *)
(***************************************************************************)
NodesVal == 1..3

\* @type: Set(Set(Int));
EdgesVal == { {1, 2}, {1, 3}, {2, 3} }

RootVal == 1

MaxCardinalityVal == 3

(***************************************************************************)
(* Constant initialization predicate for Apalache (ConstInit in the cfg).  *)
(***************************************************************************)
CInit ==
    /\ Nodes = NodesVal
    /\ Edges = EdgesVal
    /\ Root = RootVal
    /\ MaxCardinality = MaxCardinalityVal

=============================================================================