------------------------------ MODULE F ------------------------------
EXTENDS Integers

VARIABLE x

(* ------------------------------------------------------------------
   Higher-order operator Op
   Takes a set S, a unary predicate P, and a binary predicate Q.
   Returns the subset of elements of S satisfying both P(s) and Q(s, TRUE).
   ------------------------------------------------------------------ *)
Op(S, P, Q) == { s \in S : P[s] /\ Q[s, TRUE] }

(* ------------------------------------------------------------------
   Initial state: x is any element of Op applied to {1,2,3,4,5}
   with predicates:
     - P(s): s > 1
     - Q(s,b): (b = TRUE) /\ (s % 2 != 0)
   The resulting set is {3,5}, so x ∈ {3,5}.
   ------------------------------------------------------------------ *)
Init == x \in Op({1,2,3,4,5},
                 [s |-> s > 1],
                 [s,b |-> (b = TRUE) /\ (s % 2 != 0)])

(* ------------------------------------------------------------------
   Next-state relation: the system is static; x never changes.
   ------------------------------------------------------------------ *)
Next == UNCHANGED x

===============================================================================