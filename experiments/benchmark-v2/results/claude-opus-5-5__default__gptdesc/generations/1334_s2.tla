------------------------------- MODULE Utils -------------------------------
(***************************************************************************)
(* A library of utility operators over integers, sequences, finite sets   *)
(* and functions. It has no state variables, actions, temporal            *)
(* specification, fairness conditions or proofs.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Generic reduction over a finite set: folds the binary operator op      *)
(* over the elements of S, starting from the base value.                  *)
(***************************************************************************)
RECURSIVE ReduceSet(_, _, _)
ReduceSet(op(_, _), S, base) ==
  IF S = {}
    THEN base
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  op(x, ReduceSet(op, S \ {x}, base))

(***************************************************************************)
(* Sum of f[x] over all x in the finite set S.                            *)
(***************************************************************************)
Sum(f, S) == ReduceSet(LAMBDA x, acc : f[x] + acc, S, 0)

(***************************************************************************)
(* Sequence membership: e occurs somewhere in the sequence s.             *)
(***************************************************************************)
InSeq(e, s) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* Remove every occurrence of e from the sequence s.                      *)
(***************************************************************************)
Remove(s, e) == SelectSeq(s, LAMBDA x : x # e)

(***************************************************************************)
(* Range of a function.                                                   *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle(S, r): the functional graph r over the finite nonempty   *)
(* set S forms a single simple cycle through every element of S. Here     *)
(* F[i] is the (i+1)-fold composition of r. Every element returns to      *)
(* itself after exactly Cardinality(S) steps, and not after fewer steps.  *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
  LET n == Cardinality(S)
      F[i \in 0..(n - 1)] ==
        IF i = 0 THEN r
                 ELSE [x \in S |-> r[F[i - 1][x]]]
  IN  /\ S # {}
      /\ r \in [S -> S]
      /\ \A x \in S : F[n - 1][x] = x
      /\ \A x \in S : \A k \in 1..(n - 1) : F[k - 1][x] # x

=============================================================================