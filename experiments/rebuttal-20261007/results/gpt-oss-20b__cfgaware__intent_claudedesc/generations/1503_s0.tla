------------------------------ MODULE HigherOrderFilter ------------------------------
VARIABLE x

(* Generic set-filter operator that takes a set S, a unary predicate P1,
   and a binary predicate P2, returning the subset of elements satisfying
   both predicates simultaneously. *)
FilterSet(S, P1, P2) ==
  {e \in S : (P1)[e] /\ (P2)[e, TRUE]}

(* Initial state: x is set to the result of applying FilterSet to the set
   {1,2,3,4,5} with a predicate that selects elements greater than 1 and a
   binary predicate that selects odd elements paired with TRUE. *)
Init ==
  x = FilterSet({1, 2, 3, 4, 5},
                \lambda y : y > 1,
                \lambda y, z : (y Mod 2 = 1) /\ z)

(* Next state: the system remains static; no changes to x. *)
Next ==
  x' = x

=============================================================================