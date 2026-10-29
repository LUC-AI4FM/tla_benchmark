---------------------------- MODULE DuplicateNextStates ----------------------------
(***************************************************************************)
(* A very small transition system over a single variable x.  It exercises  *)
(* TLC's next-state generation and its handling of duplicate successor     *)
(* states.                                                                 *)
(*                                                                         *)
(* TLC evaluates an action disjunct by disjunct.  Each disjunct that       *)
(* assigns a value to x' produces a successor state.  If two disjuncts     *)
(* produce the same value for x', TLC generates the same successor twice.  *)
(* The second copy is a duplicate: it adds to the "generated" count but    *)
(* not to the "distinct" count.                                            *)
(*                                                                         *)
(* How a branch is written changes whether TLC produces a duplicate:       *)
(*  - A branch guarded by an obviously TRUE conjunct (TRUE /\ x' = 5)      *)
(*    still yields a successor, so it duplicates any other branch that     *)
(*    yields x' = 5.                                                       *)
(*  - A branch guarded by an obviously FALSE conjunct (FALSE /\ x' = 5)    *)
(*    is pruned before the assignment is evaluated.  It yields nothing.    *)
(*  - A branch written with a double negation, ~~(x' = 5), is not treated  *)
(*    as an assignment.  TLC treats it as a boolean test on an unbound     *)
(*    primed variable.  It therefore cannot generate a new state.  It must *)
(*    appear after x' is already bound in the same conjunction.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x

vars == <<x>>

Init == x = 42

(* Plain assignment: one successor, x' = 5. *)
A1 == x' = 5

(* Two syntactically separate disjuncts with the same value. *)
(* TLC generates the successor x = 5 twice, one duplicate.   *)
A2 == x' = 5 \/ x' = 5

(* An obviously-true guard does not suppress the branch,     *)
(* so the successor is still produced (and duplicated).      *)
A3 == (TRUE /\ x' = 5) \/ x' = 5

(* An obviously-false guard prunes the branch: no successor  *)
(* comes from the first disjunct, so there is no duplicate.  *)
A4 == (FALSE /\ x' = 5) \/ x' = 5

(* A double negation turns the assignment into a test.  The  *)
(* test runs only after x' is bound by the first conjunct.   *)
A5 == x' = 5 /\ ~~(x' = 5)

(* Self-loop from the initial state: produces x' = 42, which *)
(* is a duplicate of an already-seen state.                  *)
A6 == x = 42 /\ x' = 42

(* Once at 5, stay at 5 (avoid deadlock). *)
Stay == x = 5 /\ x' = 5

Next ==
    \/ x = 42 /\ (A1 \/ A2 \/ A3 \/ A4 \/ A5)
    \/ A6
    \/ Stay

Spec == Init /\ [][Next]_vars /\ WF_vars(x = 42 /\ A1)

-----------------------------------------------------------------------------
(* Safety: only the values 42 and 5 are ever reachable. *)
TypeOK == x \in {42, 5}

Inv == x \in {42, 5}

(* Predicate identifying the state x = 5. *)
IsFive == x = 5

(* Predicate for leaving the initial state. *)
LeftInit == x # 42

(* Action-level: leaving the initial state. *)
LeaveInit == x = 42 /\ x' # 42

(* Liveness: under weak fairness, the system eventually leaves *)
(* the initial state and reaches x = 5, and stays there.       *)
EventuallyFive == <>IsFive

EventuallyLeaves == <>LeftInit

StaysFive == [](IsFive => []IsFive)

-----------------------------------------------------------------------------
(* TLC introspection.  Exactly two distinct states (x = 42 and *)
(* x = 5) must be reported, no matter how many duplicate       *)
(* successors the disjuncts above generated.  Use this as a    *)
(* POSTCONDITION.                                              *)
NumDistinctStates == TLCGet("stats").distinct

PossibleStatesOK ==
    /\ NumDistinctStates = 2
    /\ Cardinality({v \in {42, 5} : v = 5}) = 1

=============================================================================