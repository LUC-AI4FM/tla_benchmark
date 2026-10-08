--------------------------- MODULE TLCEvalCaching ----------------------------
EXTENDS FiniteSets

(* ------------------------------------------------------------------------- *)
(*  BoundedSeq(S, n) returns the set of all sequences over S whose length
 *  is at most n.  The definition is recursive: for n = 0 we have only the
 *  empty sequence; otherwise we take all shorter sequences and append each
 *  element of S to them. *)
(* ------------------------------------------------------------------------- *)

BoundedSeq == [S, n |-> IF n = 0 THEN { <<>> }
                     ELSE BoundedSeq[S, n-1] \cup
                          { seq ^ <<x>> : seq \in BoundedSeq[S, n-1], x \in S } ]

(* ------------------------------------------------------------------------- *)
(*  Variables: Graph and TestGraph represent sets of directed edges.  Each
 *  graph is a subset of the Cartesian product of a node set with itself.
 *  For this specification we use the two‑element node set {1,2}. *)
(* ------------------------------------------------------------------------- *)

VARIABLES Graph, TestGraph

(* ------------------------------------------------------------------------- *)
(*  Initial state: choose an arbitrary input graph and a random test graph.
 *  The CHOOSE construct picks one element nondeterministically from the
 *  set of all directed graphs over {1,2}.  Once chosen, TestGraph remains
 *  fixed for the entire run. *)
(* ------------------------------------------------------------------------- *)

Init == /\ Graph \in SUBSET ({1,2} \X {1,2})
        /\ TestGraph \in SUBSET ({1,2} \X {1,2})
        /\ TestGraph = CHOOSE g \in SUBSET ({1,2} \X {1,2}) : TRUE

(* ------------------------------------------------------------------------- *)
(*  Next state: nothing changes; this guarantees that the random test
 *  graph is stable across all evaluations. *)
(* ------------------------------------------------------------------------- *)

Next == UNCHANGED <<Graph, TestGraph>>

(* ------------------------------------------------------------------------- *)
(*  Invariant capturing two key properties:
 *
 *   1) Cardinality of nested bounded sequences matches the expected
 *      values: 57 for a double‑nested construction over {1,2} with bound 2,
 *      and 65641 for a triple‑nested construction over {1,2,3} with bound 3.
 *
 *   2) Every edge in the input graph must also belong to the test graph
 *      (Graph ⊆ TestGraph).  This ensures that state variables representing
 *      edges are members of both graphs. *)
(* ------------------------------------------------------------------------- *)

Inv ==
  /\ Cardinality(BoundedSeq[BoundedSeq[{1,2}, 2], 2]) = 57
  /\ Cardinality(BoundedSeq[BoundedSeq[BoundedSeq[{1,2,3}, 3], 3], 3]) = 65641
  /\ Graph \subseteq TestGraph

=============================================================================