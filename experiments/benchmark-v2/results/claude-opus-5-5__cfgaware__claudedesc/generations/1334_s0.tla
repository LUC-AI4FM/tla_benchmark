---------------------------- MODULE Utils ----------------------------
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Fold over the co-domain of fun restricted to the integer range          *)
(* from..to, combining values with op and starting from base.              *)
(***************************************************************************)
RECURSIVE Reduce(_, _, _, _, _)
Reduce(op(_, _), fun, from, to, base) ==
    IF to < from
    THEN base
    ELSE op(fun[to], Reduce(op, fun, from, to - 1, base))

(***************************************************************************)
(* Simple addition, suitable as an argument to Reduce.                     *)
(***************************************************************************)
sum(a, b) == a + b

(***************************************************************************)
(* TRUE iff element e occurs at some position of sequence s.               *)
(***************************************************************************)
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* The sequence s with the element at index i removed.                     *)
(***************************************************************************)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(***************************************************************************)
(* The set of all values in the co-domain of function f.                   *)
(***************************************************************************)
Range(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* TRUE iff relation r (a set of ordered pairs) forms a simple cycle over  *)
(* the vertex set S: following the edges visits every vertex exactly once  *)
(* before returning to the start.                                          *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    LET n == Cardinality(S)
    IN  /\ n > 0
        /\ \E f \in [1..n -> S] :
              /\ Range(f) = S
              /\ r = { <<f[i], f[(i % n) + 1]>> : i \in 1..n }

=============================================================================