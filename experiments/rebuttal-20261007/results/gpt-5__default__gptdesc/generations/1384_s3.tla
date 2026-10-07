--------------------------- MODULE TinyGraphBSeq ---------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Helper operators for bounded sequences
*)
BSeq(S, n) ==
  UNION { [1..k -> S] : k \in 0..n }

NestedBSeq(S) ==
  BSeq(BSeq(S, 2), 2)

(*
  Helper operators for directed graphs
*)
Pair(u, v) == <<u, v>>

EdgeSet(V) == V \X V

Graph(V, E) == [ V |-> V, E |-> E ]

Nodes(g) == g.V
Edges(g) == g.E

Src(e) == e[1]
Dst(e) == e[2]

OutEdges(g, v) == { e \in Edges(g) : Src(e) = v }

Reverse(g) ==
  [ V |-> Nodes(g),
    E |-> { Pair(Dst(e), Src(e)) : e \in Edges(g) } ]

(*
  A fixed, constant graph used by the tiny state system.
  Nonempty edge set ensures RandomElement is well-defined.
*)
Gconst ==
  Graph({0, 1, 2}, { Pair(0, 1), Pair(1, 2), Pair(2, 0) })

(*
  A derived "test graph" formed by adding all reversed edges of Gconst.
  Membership of the state variables in this graph is part of the invariant.
*)
TestGraph ==
  LET r == Reverse(Gconst) IN
    [ V |-> Nodes(Gconst),
      E |-> Edges(Gconst) \cup Edges(r) ]

(*
  TLC-specific: a base set for bounded sequences and a fixed cardinality
  for the nested bounded-sequence construction. The value 57 equals
  1 + 7 + 49 where |BSeq({T,F}, 2)| = 7 and then bounded again by 2.
*)
SBase == {TRUE, FALSE}

ASSUME Cardinality(NestedBSeq(SBase)) = 57

(*
  State variables range over the edge set of Gconst.
*)
VARIABLES e1, e2

EdgeType == Edges(Gconst)

(*
  Init uses TLC-specific RandomElement under TLCEval to force evaluation
  in a particular context; TLC's caching behavior is relevant to the fixed
  cardinality check that also appears in the invariant below.
*)
Init ==
  /\ e1 = TLCEval(RandomElement(EdgeType))
  /\ e2 \in EdgeType

Next ==
  /\ e1' \in EdgeType
  /\ e2' \in EdgeType

Spec == Init /\ [][Next]_<<e1, e2>>

(*
  Safety invariants:
    - Type membership of e1, e2 in the constant graph's edge set.
    - Membership of e1, e2 in the derived test graph.
    - A fixed TLCEval-computed cardinality check on the nested bounded sequences.
*)
TypeInv ==
  /\ e1 \in EdgeType
  /\ e2 \in EdgeType

InTestGraphInv ==
  /\ e1 \in Edges(TestGraph)
  /\ e2 \in Edges(TestGraph)

CardinalityInv ==
  TLCEval(Cardinality(NestedBSeq(SBase))) = 57

Inv == TypeInv /\ InTestGraphInv /\ CardinalityInv

=============================================================================