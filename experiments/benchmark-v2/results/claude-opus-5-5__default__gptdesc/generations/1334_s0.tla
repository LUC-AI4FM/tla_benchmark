---------------------------- MODULE Utils ----------------------------
(***************************************************************************)
(* A small library of state-level mathematical utility operators over     *)
(* integers, sequences, finite sets, and functions.  The module declares  *)
(* no state variables, actions, temporal specification, fairness          *)
(* conditions or proofs.                                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Generic reduction (fold) of a binary operator op over a finite set S,  *)
(* starting from the value base.                                           *)
(***************************************************************************)
RECURSIVE ReduceSet(_, _, _)
ReduceSet(op(_, _), S, base) ==
    IF S = {}
    THEN base
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  op(x, ReduceSet(op, S \ {x}, base))

(***************************************************************************)
(* Summation helper: sum of f[x] over all x in the finite set S.          *)
(***************************************************************************)
Sum(f, S) == ReduceSet(LAMBDA x, acc : f[x] + acc, S, 0)

(***************************************************************************)
(* Sum of all elements of a set of integers.                               *)
(***************************************************************************)
SumSet(S) == ReduceSet(LAMBDA x, acc : x + acc, S, 0)

(***************************************************************************)
(* Sequence membership: element e occurs somewhere in sequence s.         *)
(***************************************************************************)
InSeq(e, s) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* Remove all occurrences of element e from sequence s.                    *)
(***************************************************************************)
Remove(s, e) == SelectSeq(s, LAMBDA x : x # e)

(***************************************************************************)
(* Remove the element at index i from sequence s.                          *)
(***************************************************************************)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(***************************************************************************)
(* Range (image) of a function f.                                          *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle(S, r): the functional graph r over the finite set S       *)
(* forms a single simple cycle through every element of S.  r must map S  *)
(* into S, and the only nonempty subset of S that is closed under r is S  *)
(* itself (so every node reaches every other node by following r).        *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    /\ S # {}
    /\ IsFiniteSet(S)
    /\ r \in [S -> S]
    /\ \A T \in SUBSET S :
          (T # {} /\ \A t \in T : r[t] \in T) => T = S

=============================================================================