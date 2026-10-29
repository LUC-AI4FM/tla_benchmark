------------------------------- MODULE Utils -------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

(***************************************************************************)
(* Reduce(op, f, from, to, base) combines the values f[from], ...,         *)
(* f[to] with the binary operator op, starting from the value base.        *)
(*                                                                         *)
(*   Reduce(op, f, from, to, base)                                         *)
(*     = op(f[to], op(f[to-1], ... op(f[from], base) ...))                 *)
(*                                                                         *)
(* f[from] is combined with base first, and each later index up to "to"    *)
(* is then combined with the accumulated result. An empty range            *)
(* (to < from) returns base.                                               *)
(***************************************************************************)
RECURSIVE Reduce(_, _, _, _, _)
Reduce(op(_, _), f, from, to, base) ==
    IF to < from
      THEN base
      ELSE op(f[to], Reduce(op, f, from, to - 1, base))

(***************************************************************************)
(* Addition, for use as a combining operator, e.g.                         *)
(*   Reduce(Plus, f, 1, n, 0) sums f[1] .. f[n].                           *)
(***************************************************************************)
Plus(a, b) == a + b

(***************************************************************************)
(* Sum of the values f[from] .. f[to].                                     *)
(***************************************************************************)
SumRange(f, from, to) == Reduce(Plus, f, from, to, 0)

(***************************************************************************)
(* Membership test: does element e appear anywhere in sequence s?          *)
(***************************************************************************)
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* Remove the element at position i of sequence s. The result is one       *)
(* element shorter, and every other element keeps its relative order.      *)
(***************************************************************************)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(***************************************************************************)
(* The set of all values in the range of function f.                       *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle(S, r) holds when the function r, viewed as a directed     *)
(* graph in which x has an edge to r[x], forms a single simple cycle       *)
(* through every element of the finite, non-empty set S. Starting from an  *)
(* element of S and following r, the walk visits each element of S        *)
(* exactly once and then returns to its starting point.                    *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    /\ S # {}
    /\ S \subseteq DOMAIN r
    /\ LET n     == Cardinality(S)
           start == CHOOSE x \in S : TRUE
           walk[i \in 1..n] == IF i = 1 THEN start ELSE r[walk[i - 1]]
       IN  /\ Range(walk) = S
           /\ \A i, j \in 1..n : i # j => walk[i] # walk[j]
           /\ r[walk[n]] = start

=============================================================================