------------------------------- MODULE Utils -------------------------------
(***************************************************************************)
(* A library of state-level mathematical utility operators over integers, *)
(* sequences, finite sets, and functions.                                  *)
(*                                                                         *)
(* The described library has no state variables, actions, temporal        *)
(* specification, fairness or proofs. A trivial stuttering harness         *)
(* (VARIABLES, Init, Next, Spec) is appended only to satisfy the required  *)
(* module format. It does not affect the meaning of any operator.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

-----------------------------------------------------------------------------
(***************************************************************************)
(* Generic reduction over a finite set.                                    *)
(* Folds the binary operator Op over the elements of S, starting from      *)
(* the accumulator value.                                                  *)
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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Sequence utilities.                                                     *)
(***************************************************************************)

\* TRUE iff the element e occurs in the sequence s.
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

\* The sequence s with every occurrence of e removed.
Remove(s, e) == SelectSeq(s, LAMBDA t : t # e)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Function utilities.                                                     *)
(***************************************************************************)

\* The range (image) of a function f.
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle(S, r): the finite functional graph r over S forms one     *)
(* simple cycle through every element of S.                                *)
(*                                                                         *)
(* r must be a function from S to S. Let F[i] be the i-fold composition    *)
(* of r. Then from every node s in S, the nodes reached in 1..|S| steps    *)
(* must be exactly S. So r is a single cyclic permutation of S.            *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    LET N == Cardinality(S)
        F[i \in 1..N] ==
            IF i = 1 THEN r
                     ELSE [j \in S |-> r[F[i - 1][j]]]
    IN  /\ r \in [S -> S]
        /\ \A s \in S : { F[j][s] : j \in 1..N } = S

-----------------------------------------------------------------------------
(***************************************************************************)
(* Trivial harness (format only): a single unused variable that never      *)
(* changes. The library itself defines no state.                           *)
(***************************************************************************)
VARIABLES dummy

vars == << dummy >>

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_vars

=============================================================================