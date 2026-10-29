------------------------------- MODULE APSpanTree -------------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the SpanTree specification.  It declares *)
(* the constants and variables of SpanTree with type annotations, supplies *)
(* concrete constant values for a small three-node graph (used by          *)
(* APSpanTree.cfg), and instantiates SpanTree rather than redefining its   *)
(* behavior locally.                                                        *)
(***************************************************************************)
EXTENDS Integers

\* Concrete example values for a small three-node graph.
NodesVal == {"a", "b", "c"}

EdgesVal == {{"a", "b"}, {"a", "c"}, {"b", "c"}}

RootVal == "a"

CONSTANTS
    \* @type: Set(Str);
    Nodes,
    \* @type: Set(Set(Str));
    Edges,
    \* @type: Str;
    Root,
    \* @type: Int;
    MaxCardinality

VARIABLES
    \* @type: Str -> Str;
    mom,
    \* @type: Str -> Int;
    dist

\* All behavior (Init, Next, Spec, TypeOK, properties) comes from SpanTree.
INSTANCE SpanTree
=============================================================================