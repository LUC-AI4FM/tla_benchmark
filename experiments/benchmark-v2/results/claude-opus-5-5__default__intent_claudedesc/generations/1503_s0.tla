---------------------------- MODULE HigherOrderFilter ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

(***************************************************************************)
(* Generic set filter: takes a set S, a unary predicate P(_) and a binary  *)
(* predicate Q(_,_), and returns the elements of S that satisfy both       *)
(* predicates at once. Each element e is checked with Q(e, TRUE), so the   *)
(* binary predicate sees the element paired with the Boolean TRUE.         *)
(***************************************************************************)
Filter(S, P(_), Q(_, _)) == { e \in S : P(e) /\ Q(e, TRUE) }

BaseSet == {1, 2, 3, 4, 5}

(* Unary predicate: element greater than 1 *)
GreaterThanOne == LAMBDA n : n > 1

(* The demonstration result, built with LAMBDA expressions passed inline.  *)
(* It should equal {3, 5}.                                                *)
Result ==
    Filter(BaseSet,
           LAMBDA n : n > 1,
           LAMBDA n, b : (n % 2 = 1) /\ b)

Init == x \in Result

(* The system stays static: no state changes after initialization *)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Well-formedness checks                                                   *)
(***************************************************************************)
TypeOK == x \in BaseSet

ResultCorrect == Result = {3, 5}

InResult == x \in Result

THEOREM Spec => [](TypeOK /\ InResult)
==================================================================================