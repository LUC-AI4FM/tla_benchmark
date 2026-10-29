------------------------------- MODULE DuplicateSuccessors -------------------------------
(***************************************************************************)
(* A very small transition system over a single variable x.  It exercises  *)
(* how TLC generates next states and handles duplicate successor states.   *)
(*                                                                         *)
(* TLC evaluates an action formula by walking its disjuncts left to right. *)
(* For each disjunct it reaches a primed-variable assignment such as       *)
(* x' = 5, and it produces one candidate successor state.  It does not     *)
(* deduplicate syntactically different disjuncts that yield the same       *)
(* successor.  So every disjunct that assigns the same value creates a     *)
(* duplicate candidate.  TLC then removes the duplicates when it           *)
(* fingerprints the new states, so they are generated but counted once    *)
(* as distinct states.                                                     *)
(*                                                                         *)
(*  - An obviously true guard (TRUE /\ x' = 5) does not stop TLC from      *)
(*    evaluating the assignment, so it yields another duplicate.           *)
(*  - An obviously false guard (FALSE /\ x' = 7) short-circuits before the *)
(*    assignment, so it yields no successor at all.                        *)
(*  - Double negation ~~(x' = 5) hides the assignment from TLC's           *)
(*    assignment detection.  When x' is not yet bound, TLC cannot treat    *)
(*    the formula as an assignment and reports an error.  When x' is       *)
(*    already bound by an earlier conjunct, TLC evaluates it as an         *)
(*    ordinary boolean test, which filters successors instead of creating  *)
(*    them.                                                                *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

-----------------------------------------------------------------------------
Init == x = 42

\* Plain assignment: one successor with x = 5.
A1 == x' = 5

\* Assignment repeated through a separate disjunct: a duplicate successor.
A2 == x' = 5 \/ x' = 5

\* Obviously true guard: the assignment is still evaluated, so a duplicate.
A3 == TRUE /\ x' = 5

\* Obviously false guard: short-circuits, so no successor is generated.
A4 == FALSE /\ x' = 7

\* Double negation used as a test after x' is bound by the first conjunct.
\* It filters successors and does not generate them.
A5 == x' = 5 /\ ~~(x' = 5)

\* Disjunction whose second branch is false once x' = 5 is fixed.
A6 == x' = 5 /\ (x' = 5 \/ x' = 6)

Next == A1 \/ A2 \/ A3 \/ A4 \/ A5 \/ A6

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety: only the initial value and 5 are reachable.
TypeOK == x \in {42, 5}

Inv == x \in {42, 5}

\* The state x = 5.
IsFive == x = 5

\* The system has left the initial state.
LeftInit == x # 42

\* Liveness: x eventually becomes 5 and then stays different from 42.
EventuallyFive == <>IsFive

EventuallyLeaves == <>[]LeftInit

\* TLC introspection: TLC must report exactly two distinct states (x = 42
\* and x = 5).  Duplicate successors must not inflate the distinct count.
\* Check this as a POSTCONDITION.
CheckStates ==
    /\ TLCGet("stats").distinct = 2
    /\ TLCGet("stats").generated >= TLCGet("stats").distinct

\* Selected predicates hold for exactly the expected number of states.
PossibleStates(P) == Cardinality({v \in {42, 5} : P[v]})

FiveCount == {v \in {42, 5} : v = 5}
LeftCount == {v \in {42, 5} : v # 42}

CheckPredicates ==
    /\ FiveCount = {5}
    /\ LeftCount = {5}
=============================================================================