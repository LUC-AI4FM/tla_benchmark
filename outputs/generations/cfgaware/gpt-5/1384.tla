---- MODULE HelpersAndTinySystem ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Helper operators for bounded sequences and directed graphs.
  The spec uses TLC-specific operators TLCEval and RandomElement to force
  evaluation of certain expressions in a concrete TLC context. This matters
  for TLC's internal caching: wrapping with TLCEval anchors the evaluation
  so that the same subexpression does not get re-evaluated in a different
  context across state transitions.
*)

(*
  BSeq(n, S) is the set of all sequences over S whose length is at most n.
  For k = 0, [1..0 -> S] is the singleton set containing the empty sequence << >>.
*)
BSeq(n, S) == UNION { [1..k -> S] : k \in 0..n }

(*
  Simple directed-graph utilities.
  A graph is a record [ Nodes |-> N, Edges |-> E ] with Edges ⊆ Nodes × Nodes.
*)
IsGraph(g) ==
  /\ "Nodes" \in DOMAIN g
  /\ "Edges" \in DOMAIN g
  /\ g.Edges \subseteq g.Nodes \X g.Nodes

Nodes(g) == g.Nodes
Edges(g) == g.Edges

(*
  A fixed constant graph value used by the tiny transition system below.
  Nodes are {0,1,2} and edges form a 3-cycle.
*)
Graph ==
  [ Nodes |-> {0, 1, 2}
  , Edges |-> { <<0, 1>>, <<1, 2>>, <<2, 0>> }
  ]

(*
  TestGraph is a derived graph that extends Graph with a self-loop on a
  single node chosen (once) by TLC via RandomElement. The argument of
  RandomElement and the base edge set are both wrapped in TLCEval to
  force evaluation in a stable context and avoid re-selection under TLC caching.
*)
TestGraph ==
  LET seed == TLCEval(RandomElement(Nodes(Graph)))
      base == TLCEval(Edges(Graph))
  IN [ Nodes |-> Nodes(Graph)
     , Edges |-> base \cup { <<seed, seed>> }
     ]

ASSUME IsGraph(Graph)

(*
  An assumption about the cardinality of a nested bounded-sequence construction.
  BSeq(1, {0,1}) has 3 elements: << >>, <<0>>, <<1>>.
  Hence BSeq(2, BSeq(1, {0,1})) has 1 + 3 + 3^2 = 13 sequences.
*)
ASSUME Cardinality(BSeq(2, BSeq(1, {0,1}))) = 13

(*
  Tiny state system: two variables e and f range over the edge set of Graph.
*)
VARIABLES e, f

(*
  Init uses TLC RandomElement wrapped in TLCEval to pick concrete initial
  edges from the (constant) Graph edge set.
*)
Init ==
  LET u == TLCEval(RandomElement(Edges(Graph)))
      v == TLCEval(RandomElement(Edges(Graph)))
  IN /\ e = u
     /\ f = v

(*
  Next either stutters or re-picks e' and f' by RandomElement on the
  (constant) Graph edge set, again wrapped in TLCEval to force evaluation.
*)
Next ==
  \/ LET u == TLCEval(RandomElement(Edges(Graph)))
         v == TLCEval(RandomElement(Edges(Graph)))
     IN /\ e' = u
        /\ f' = v
  \/ UNCHANGED <<e, f>>

(*
  Invariant:
    - e and f are edges of Graph (type membership),
    - and also edges of the derived TestGraph,
    - and the TLCEval-computed cardinality check equals the fixed value 13.
  The TLCEval on the cardinality ensures the arithmetic expression is
  evaluated in TLC's concrete context (and cached accordingly).
*)
Inv ==
  /\ e \in Edges(Graph)
  /\ f \in Edges(Graph)
  /\ e \in Edges(TestGraph)
  /\ f \in Edges(TestGraph)
  /\ TLCEval(Cardinality(BSeq(2, BSeq(1, {0,1})))) = 13

====