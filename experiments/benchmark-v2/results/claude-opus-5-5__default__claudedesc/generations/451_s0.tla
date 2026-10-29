--------------------------- MODULE test61 ---------------------------
(***************************************************************************)
(* Tests parameterized instantiation of module test61a, comparing two     *)
(* equivalent ways of instantiating it with the parameter x replaced by    *)
(* the variable y.                                                         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

(***************************************************************************)
(* Approach 1: parameterized instantiation.                               *)
(***************************************************************************)
IM(x) == INSTANCE test61a

ISpec == IM(y)!Spec

(***************************************************************************)
(* Approach 2: direct instantiation with explicit substitution.           *)
(***************************************************************************)
JM == INSTANCE test61a WITH x <- y

JSpec == JM!Spec

(***************************************************************************)
(* Initial predicate and next-state relation, imported from test61a      *)
(* through the parameterized instantiation.                               *)
(***************************************************************************)
Init == IM(y)!Init

Next == IM(y)!Next

(***************************************************************************)
(* The specification to check is ISpec.                                   *)
(***************************************************************************)
Spec == ISpec

(***************************************************************************)
(* Safety invariant: y stays between 0 and 4.                             *)
(***************************************************************************)
Invariant == y \in 0..4

THEOREM ISpec => []Invariant
THEOREM ISpec <=> JSpec
=============================================================================