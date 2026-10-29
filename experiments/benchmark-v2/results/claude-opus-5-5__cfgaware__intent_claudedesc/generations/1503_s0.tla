---------------------------- MODULE HigherOrderFilter ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

(* Generic filter: keeps the elements of S that satisfy the unary predicate P *)
(* and the binary predicate Q, where Q pairs each element with TRUE.          *)
Filter(S, P(_), Q(_, _)) == { e \in S : P(e) /\ Q(e, TRUE) }

(* Result is {3, 5}: elements greater than 1 that are odd. *)
Result == Filter({1, 2, 3, 4, 5},
                 LAMBDA a : a > 1,
                 LAMBDA a, b : (a % 2 = 1) /\ b)

Init == x \in Result

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in Result
==================================================================================