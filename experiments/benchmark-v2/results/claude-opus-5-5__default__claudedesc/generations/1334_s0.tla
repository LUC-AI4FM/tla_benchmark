------------------------------- MODULE Utils -------------------------------
(***************************************************************************)
(* A library of auxiliary operators for use by other specifications.       *)
(* It declares no CONSTANTS or VARIABLES and defines no behaviors.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Reduce: fold over the co-domain of fun on the index range from..to,     *)
(* combining values with the binary operator op, starting from base.      *)
(***************************************************************************)
RECURSIVE Reduce(_, _, _, _, _)
Reduce(op(_, _), fun, from, to, base) ==
    IF to < from
    THEN base
    ELSE op(fun[to], Reduce(op, fun, from, to - 1, base))

(***************************************************************************)
(* sum: simple addition, usable as the operator argument of Reduce.        *)
(***************************************************************************)
sum(a, b) == a + b

(***************************************************************************)
(* Contains: TRUE iff element e occurs at some position of sequence s.     *)
(***************************************************************************)
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* RemoveAt: the sequence s with the element at index i removed.           *)
(***************************************************************************)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(***************************************************************************)
(* Range: the set of all values in the co-domain of function f.            *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle: TRUE iff relation r (a set of pairs) forms a simple      *)
(* cycle over vertex set S. Each vertex must have exactly one successor.   *)
(* Following the edges from a start vertex must visit every vertex         *)
(* exactly once and then return to the start.                              *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    LET n == Cardinality(S)
        start == CHOOSE x \in S : TRUE
        F[i \in 1..n] ==
            IF i = 1
            THEN start
            ELSE CHOOSE y \in S : <<F[i - 1], y>> \in r
    IN  /\ S # {}
        /\ r \subseteq S \X S
        /\ \A x \in S : \E! y \in S : <<x, y>> \in r
        /\ Range(F) = S
        /\ <<F[n], F[1]>> \in r

=============================================================================