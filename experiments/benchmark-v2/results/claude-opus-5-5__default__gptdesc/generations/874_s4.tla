------------------------------ MODULE APSpanTree ------------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the SpanTree specification.               *)
(* Provides type annotations for constants and variables, concrete         *)
(* constant values for a small three-node graph (used by APSpanTree.cfg),  *)
(* and instantiates SpanTree instead of redefining its behavior.           *)
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

vars == <<mom, dist>>

(***************************************************************************)
(* Instantiate the original spanning-tree specification.                   *)
(***************************************************************************)
ST == INSTANCE SpanTree

(***************************************************************************)
(* Concrete constant values for a three-node graph (Apalache ConstInit).   *)
(***************************************************************************)
CInit ==
    /\ Nodes = {1, 2, 3}
    /\ Edges = {{1, 2}, {2, 3}, {1, 3}}
    /\ Root = 1
    /\ MaxCardinality = 3

(***************************************************************************)
(* Behavior is taken entirely from SpanTree.                               *)
(***************************************************************************)
Init == ST!Init

Next == ST!Next

Spec == ST!Spec

(***************************************************************************)
(* A local type invariant for the instantiated variables.                  *)
(***************************************************************************)
TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat]

=============================================================================