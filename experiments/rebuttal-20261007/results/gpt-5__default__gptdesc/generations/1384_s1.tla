----------------------------- MODULE BSeqGraphTiny -----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

(*
  Helper operators for bounded sequences and directed graphs, plus
  a tiny state system whose variables range over the edge set of a
  constant graph. TLC-specific TLCEval and RandomElement are used
  to force evaluation in a particular context; TLC's caching can
  affect when/where expressions are evaluated.
*)

(*
  Cartesian product of two sets as pairs.
*)
XProd(A, B) == { <<a, b>> : a \in A, b \in B }

(*
  Bounded sequences: all finite sequences over S of length <= n.
*)
BSeq(S, n) == { s \in Seq(S) : Len(s) <= n }

(*
  Simple directed-graph shape and helpers. A graph is a record
  with fields V (vertices) and E (edges subset of V × V).
*)
IsGraph(G) ==
  /\ DOMAIN G = {"V", "E"}
  /\ G.E \subseteq XProd(G.V, G.V)

VerticesOf(G) == G.V
EdgesOf(G) == G.E

(*
  A derived “test graph” that augments G with all self-loops.
  This ensures EdgesOf(G) ⊆ EdgesOf(DerivedTestGraph(G)).
*)
DerivedTestGraph(G) ==
  LET loops == { <<v, v>> : v \in G.V }
  IN [ V |-> G.V, E |-> G.E \cup loops ]

(*
  An assumption about the cardinality of a nested bounded-sequence
  construction. With S = {0,1}, |BSeq(S,2)| = 1 + 2 + 4 = 7, and
  |BSeq(BSeq(S,2),2)| = 1 + 7 + 7^2 = 57.
*)
ASSUME Cardinality(BSeq(BSeq({0,1}, 2), 2)) = 57

(*
  State variables range over the edge set of a constant graph.
*)
CONSTANT G0

VARIABLES e1, e2

vars == << e1, e2 >>

Init ==
  /\ IsGraph(G0)
  /\ e1 \in EdgesOf(G0)
  /\ e2 \in EdgesOf(G0)

Next ==
  /\ e1' \in EdgesOf(G0)
  /\ e2' \in EdgesOf(G0)

(*
  TLC-specific cardinality check computed via TLCEval in a context
  constructed with RandomElement to force evaluation in a particular
  state context (important for TLC caching behavior).
*)
CardinalityFix ==
  LET inner  == BSeq({0,1}, 2)
      outer  == BSeq(inner, 2)
      forced == RandomElement({ outer })  \* singleton, non-empty
      val    == TLCEval(Cardinality(forced))
  IN val = 57

TypeInv ==
  /\ e1 \in EdgesOf(G0)
  /\ e2 \in EdgesOf(G0)

DerivedInv ==
  LET TG == DerivedTestGraph(G0)
  IN /\ e1 \in EdgesOf(TG)
     /\ e2 \in EdgesOf(TG)

Inv == TypeInv /\ DerivedInv /\ CardinalityFix

Spec == Init /\ [][Next]_vars

=============================================================================