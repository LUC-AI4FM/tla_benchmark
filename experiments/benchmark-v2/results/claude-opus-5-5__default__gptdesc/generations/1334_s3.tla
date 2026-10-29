------------------------------- MODULE Utils -------------------------------
(***************************************************************************)
(* A small library of utility operators over integers, sequences, finite  *)
(* sets and functions.  This module declares no state variables, actions, *)
(* temporal specification, fairness conditions or proofs.  It contains    *)
(* only state-level mathematical operators.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Generic reduction over a finite set.  Op is applied to every element   *)
(* of S in some order, accumulating from the initial value `value`.        *)
(***************************************************************************)
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) ==
    IF S = {}
    THEN value
    ELSE LET s == CHOOSE x \in S : TRUE
         IN  SetReduce(Op, S \ {s}, Op(s, value))

(***************************************************************************)
(* Summation helper: the sum of f[x] over all x in the finite set S.      *)
(***************************************************************************)
Sum(f, S) == SetReduce(LAMBDA x, acc : f[x] + acc, S, 0)

(***************************************************************************)
(* Sequence membership: TRUE iff element e occurs somewhere in seq s.     *)
(***************************************************************************)
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* Sequence removal: s with every occurrence of e removed.                *)
(***************************************************************************)
Remove(s, e) == SelectSeq(s, LAMBDA t : t # e)

(***************************************************************************)
(* The range (image) of a function.                                       *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle(S, r) holds when r is a function from S to S whose        *)
(* functional graph is one simple cycle through every element of S.       *)
(* Iterating r from any start s visits all of S within |S| steps.         *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    LET n == Cardinality(S)
        F[i \in 1..n] ==
            IF i = 1 THEN r
                     ELSE [j \in S |-> r[F[i - 1][j]]]
    IN  /\ r \in [S -> S]
        /\ \A s \in S : { F[i][s] : i \in 1..n } = S

=============================================================================