---------------------------- MODULE Utils ----------------------------
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Generic reduction over a finite set: folds op over the elements of set, *)
(* starting from the accumulator acc.                                      *)
(***************************************************************************)
RECURSIVE Reduce(_, _, _)
Reduce(op(_, _), set, acc) ==
    IF set = {}
    THEN acc
    ELSE LET x == CHOOSE y \in set : TRUE
         IN  Reduce(op, set \ {x}, op(x, acc))

(***************************************************************************)
(* Summation of f[x] over all x in the finite set S.                       *)
(***************************************************************************)
Sum(f, S) == Reduce(LAMBDA x, acc : acc + f[x], S, 0)

(***************************************************************************)
(* Sequence membership.                                                    *)
(***************************************************************************)
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* Remove the element at index i from sequence s.                          *)
(***************************************************************************)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(***************************************************************************)
(* Range of a function.                                                    *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* A functional graph r over the finite set S forms a simple cycle iff r   *)
(* maps S into S and no nonempty proper subset of S is closed under r.     *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    /\ S # {}
    /\ r \in [S -> S]
    /\ \A T \in SUBSET S :
          (T # {} /\ \A x \in T : r[x] \in T) => T = S

=============================================================================