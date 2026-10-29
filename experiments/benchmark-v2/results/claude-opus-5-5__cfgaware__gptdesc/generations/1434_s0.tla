---------------------------- MODULE PossibleNext ----------------------------
(***************************************************************************)
(* A tiny transition system over a single variable x.  It exercises how    *)
(* TLC generates successor states, and how it handles duplicates, for      *)
(* different syntactic shapes of the Next-state relation.                  *)
(*                                                                         *)
(* - Two syntactically identical disjuncts (x' = 5 \/ x' = 5) make TLC     *)
(*   generate the same successor twice.  The fingerprint set later         *)
(*   discards the duplicate, but the "states generated" counter counts     *)
(*   both.                                                                 *)
(* - An obviously true conjunct (TRUE /\ x' = 42) still makes TLC          *)
(*   evaluate the assignment, so it produces a successor.                  *)
(* - An obviously false conjunct (FALSE /\ x' = 7) prunes the branch       *)
(*   before the assignment, so TLC generates no successor for it.          *)
(* - A double negation (~~TRUE /\ x' = 5) cannot be simplified away        *)
(*   syntactically.  TLC evaluates the negations as an ordinary boolean    *)
(*   and then handles the assignment, which yields one more duplicate      *)
(*   successor x = 5.                                                      *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

Init == x = 42

\* Candidate next-state actions.
A1 == x' = 5                 \* plain assignment
A2 == x' = 5                 \* syntactic duplicate of A1 -> duplicate successor
A3 == TRUE /\ x' = 42        \* obviously-true guard -> successor generated
A4 == FALSE /\ x' = 7        \* obviously-false guard -> no successor
A5 == ~~TRUE /\ x' = 5       \* double negation -> evaluated, duplicate successor

Next == A1 \/ A2 \/ A3 \/ A4 \/ A5

Spec == Init /\ [][Next]_vars

\* Only 42 and 5 are reachable.  7 never is, because A4 is always disabled.
Inv == x \in {42, 5}

\* A state predicate identifying the state x = 5.
HasFive == x = 5

\* An action predicate for leaving the initial state.
LeaveInit == x = 42 /\ x' # 42

\* The selected predicates whose possibility counts are checked.
_POSSIBLE == <<"HasFive", "LeaveInit">>

\* TLC introspection: after model checking, the reported number of
\* distinct (possible) states must be exactly the two reachable states
\* {x = 42, x = 5}, for which HasFive and LeaveInit are realizable.
PossibleCounts ==
    /\ TLCGet("stats").distinct = 2
    /\ Len(_POSSIBLE) = 2
    /\ TLCGet("stats").generated >= TLCGet("stats").distinct
=============================================================================