------------------------------- MODULE Utils -------------------------------
(***************************************************************************)
(* A library of utility operators over integers, sequences, finite sets,   *)
(* and functions. This module has no state variables, actions, temporal    *)
(* specification, fairness conditions, or proofs. It contains only         *)
(* state-level mathematical operators.                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Generic reduction over a finite set. Starting from the accumulator acc, *)
(* it repeatedly picks an element x of the remaining set and replaces the  *)
(* accumulator with op(x, acc). The result is well defined when op is      *)
(* commutative and associative in the appropriate sense.                   *)
(***************************************************************************)
ReduceSet(op(_, _), set, acc) ==
    LET RECURSIVE R(_, _)
        R(s, a) ==
            IF s = {}
               THEN a
               ELSE LET x == CHOOSE y \in s : TRUE
                    IN  R(s \ {x}, op(x, a))
    IN  R(set, acc)

(***************************************************************************)
(* Sum of f[x] over all x in the finite set S.                             *)
(***************************************************************************)
Sum(f, S) == ReduceSet(LAMBDA x, a : f[x] + a, S, 0)

(***************************************************************************)
(* Sequence membership: TRUE iff e occurs somewhere in the sequence s.     *)
(***************************************************************************)
InSeq(s, e) == \E i \in 1..Len(s) : s[i] = e

(***************************************************************************)
(* Remove every occurrence of e from the sequence s and keep the order of  *)
(* the remaining elements.                                                 *)
(***************************************************************************)
Remove(s, e) == SelectSeq(s, LAMBDA t : t # e)

(***************************************************************************)
(* The range (image) of a function.                                        *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* IsSimpleCycle(S, r): the functional graph r forms a single simple       *)
(* cycle over the nonempty finite set S. r must be a function from S into  *)
(* S. Starting from any node and following r, every node of S must be      *)
(* reachable within Cardinality(S) steps.                                  *)
(***************************************************************************)
IsSimpleCycle(S, r) ==
    LET F[n \in Nat] ==
            IF n = 0
               THEN [x \in S |-> x]
               ELSE [x \in S |-> r[F[n - 1][x]]]
    IN  /\ S # {}
        /\ IsFiniteSet(S)
        /\ DOMAIN r = S
        /\ Range(r) \subseteq S
        /\ \A x, y \in S :
              \E n \in 1..Cardinality(S) : F[n][x] = y

=============================================================================