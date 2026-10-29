-------------------------- MODULE TLCStateGeneration --------------------------
(***************************************************************************)
(* Test harness for TLC's successor-state generation.                      *)
(*                                                                         *)
(* Starting from one initial state (x = 0), several next-state actions     *)
(* produce successor states. Each action arranges its conjunctions and     *)
(* disjunctions differently:                                               *)
(*                                                                         *)
(*   A1 : assignment x' placed before a disjunction of TRUE conditions     *)
(*   A2 : assignment x' placed after a disjunction of TRUE conditions      *)
(*   A3 : double negation ~~(TRUE \/ TRUE), so the disjunction is          *)
(*        evaluated eagerly as a boolean and not enumerated                *)
(*   A4 : disjunction with an unsatisfiable (FALSE) branch                 *)
(*   A5 : simple disjunction between two different assignments            *)
(*                                                                         *)
(* Each action ends with Count(i). Count(i) increments TLC register i each *)
(* time TLC evaluates the action to a possible successor. The final        *)
(* register values show whether TLC generated duplicate states internally, *)
(* even though the set of distinct reachable states stays the same.        *)
(*                                                                         *)
(* Suggested TLC configuration:                                            *)
(*   INIT Init   NEXT Next                                                 *)
(*   INVARIANT TypeOK  NoSpuriousStates  Reachable                         *)
(*   POSTCONDITION PostCondition                                           *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    ExpA1,   \* expected number of times A1 yields a successor
    ExpA2,   \* expected number of times A2 yields a successor
    ExpA3,   \* expected number of times A3 yields a successor
    ExpA4,   \* expected number of times A4 yields a successor
    ExpA5    \* expected number of times A5 yields a successor (both branches)

ASSUME /\ ExpA1 \in Nat
       /\ ExpA2 \in Nat
       /\ ExpA3 \in Nat
       /\ ExpA4 \in Nat
       /\ ExpA5 \in Nat

VARIABLES x

vars == << x >>

Counters == 1..5

(* Increment TLC register i. This expression is always TRUE. *)
Count(i) == TLCSet(i, TLCGet(i) + 1)

ExpectedStates == {0, 1, 2, 3, 4, 5, 6}

SpuriousValue == 99

-----------------------------------------------------------------------------
Init ==
    /\ x = 0
    /\ \A i \in Counters : TLCSet(i, 0)

(* Assignment appears before a disjunction of always-true conditions. *)
A1 ==
    /\ x = 0
    /\ x' = 1
    /\ (TRUE \/ TRUE)
    /\ Count(1)

(* Assignment appears after a disjunction of always-true conditions. *)
A2 ==
    /\ x = 0
    /\ (TRUE \/ TRUE)
    /\ x' = 2
    /\ Count(2)

(* Double negation forces the disjunction to be evaluated eagerly. *)
A3 ==
    /\ x = 0
    /\ ~~(TRUE \/ TRUE)
    /\ x' = 3
    /\ Count(3)

(* Disjunction with an unsatisfiable branch. *)
A4 ==
    /\ x = 0
    /\ \/ (FALSE /\ x' = SpuriousValue)
       \/ x' = 4
    /\ Count(4)

(* Simple disjunction between different variable assignments. *)
A5 ==
    /\ x = 0
    /\ \/ x' = 5
       \/ x' = 6
    /\ Count(5)

(* Terminal states stutter so that TLC reports no deadlock. *)
Done ==
    /\ x # 0
    /\ UNCHANGED x

Next == A1 \/ A2 \/ A3 \/ A4 \/ A5 \/ Done

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == x \in Nat

(* Only the intended successor states are reachable. *)
Reachable == x \in ExpectedStates

(* States from unsatisfiable branches never appear. *)
NoSpuriousStates == x # SpuriousValue

THEOREM Spec => [](TypeOK /\ Reachable /\ NoSpuriousStates)

-----------------------------------------------------------------------------
(* Checked by TLC after exploration finishes (POSTCONDITION).              *)
(*                                                                         *)
(* StateSpaceExact: exactly the expected states were found, no more and    *)
(* no fewer.                                                               *)
(*                                                                         *)
(* TransitionCounts: each action was considered exactly the expected       *)
(* number of times. This reveals duplicate generation. For example, A1     *)
(* and A2 enumerate (TRUE \/ TRUE) once per branch, giving 2 each. A3,     *)
(* with double negation, gives 1. A4 gives 1. A5 gives 2, one for each     *)
(* distinct branch.                                                        *)

StateSpaceExact == TLCGet("distinct") = Cardinality(ExpectedStates)

TransitionCounts ==
    /\ TLCGet(1) = ExpA1
    /\ TLCGet(2) = ExpA2
    /\ TLCGet(3) = ExpA3
    /\ TLCGet(4) = ExpA4
    /\ TLCGet(5) = ExpA5

PostCondition == StateSpaceExact /\ TransitionCounts

Cardinality(S) ==
    LET CS[T \in SUBSET S] ==
            IF T = {} THEN 0
            ELSE LET e == CHOOSE e \in T : TRUE IN 1 + CS[T \ {e}]
    IN CS[S]

=============================================================================