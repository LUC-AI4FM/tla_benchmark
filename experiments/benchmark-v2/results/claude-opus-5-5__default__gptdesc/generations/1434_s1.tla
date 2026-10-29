--------------------------- MODULE DuplicateNextStates ---------------------------
(***************************************************************************)
(* A tiny transition system over a single variable x.  It exercises how    *)
(* TLC generates successor states and how it handles duplicate successor  *)
(* states produced by the different disjuncts of a next-state action.      *)
(*                                                                         *)
(* TLC evaluates an action disjunct by disjunct.  Each disjunct that       *)
(* assigns x' produces a successor state.  If two disjuncts assign the     *)
(* same value, TLC generates that successor twice.  The duplicate is only  *)
(* removed later, when TLC looks up the state's fingerprint in its seen    *)
(* set.  The number of generated states can therefore be larger than the   *)
(* number of distinct states.                                              *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

Init == x = 42

(***************************************************************************)
(* Two syntactically identical disjuncts.  TLC generates the successor     *)
(* x = 5 twice.                                                            *)
(***************************************************************************)
NextDup ==
    \/ x' = 5
    \/ x' = 5

(***************************************************************************)
(* The second branch is guarded by a conjunct that is obviously true.      *)
(* TLC still explores the branch, so x = 5 is again generated twice.       *)
(***************************************************************************)
NextTrueBranch ==
    \/ x' = 5
    \/ /\ TRUE
       /\ x' = 5

(***************************************************************************)
(* The second branch is guarded by a conjunct that is obviously false.     *)
(* TLC prunes the branch before reaching the assignment, so it generates   *)
(* no successor and no duplicate.                                          *)
(***************************************************************************)
NextFalseBranch ==
    \/ x' = 5
    \/ /\ FALSE
       /\ x' = 7

(***************************************************************************)
(* With double negation, TLC no longer treats x' = 5 as an assignment.     *)
(* It treats it as a boolean test that can only be evaluated after x' has  *)
(* been bound.  The first disjunct therefore binds nothing by itself.      *)
(* Only the second disjunct generates the successor, so there is no        *)
(* duplicate.                                                              *)
(***************************************************************************)
NextDoubleNeg ==
    \/ /\ x' = 5
       /\ ~~(x' = 5)
    \/ x' = 5

(***************************************************************************)
(* An action that assigns a different value only in the initial state.     *)
(***************************************************************************)
NextOther ==
    /\ x = 42
    /\ x' = 5

Next ==
    \/ NextDup
    \/ NextTrueBranch
    \/ NextFalseBranch
    \/ NextDoubleNeg
    \/ NextOther

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: only the initial value and 5 are reachable.                     *)
Inv == x \in {42, 5}

TypeOK == x \in Nat

(* Predicate identifying the state x = 5.                                  *)
IsFive == x = 5

(* Predicate (action) for leaving the initial state.                       *)
LeaveInit == x = 42 /\ x' # 42

(* Liveness: the system eventually reaches x = 5 and stays there.          *)
EventuallyFive == <>IsFive

StaysFive == <>[]IsFive

(* Every step out of the initial state goes to x = 5.                      *)
LeaveProp == [][LeaveInit => x' = 5]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* TLC introspection.  After model checking, TLC reports the numbers of    *)
(* generated and distinct states.  There are exactly two distinct states,  *)
(* x = 42 and x = 5.  The duplicate successors from NextDup and            *)
(* NextTrueBranch make the generated count strictly larger than the        *)
(* distinct count.                                                         *)
(***************************************************************************)
Stats == TLCGet("stats")

PostCondition ==
    /\ Stats.distinct = Cardinality({42, 5})
    /\ Stats.generated >= Stats.distinct

(* Number of possible states for selected predicates.                      *)
NumStatesOf(P(_)) == Cardinality({v \in {42, 5} : P(v)})

IsFiveVal(v) == v = 5
IsInitVal(v) == v = 42

CheckCounts ==
    /\ NumStatesOf(IsFiveVal) = 1
    /\ NumStatesOf(IsInitVal) = 1
    /\ Stats.distinct = NumStatesOf(IsFiveVal) + NumStatesOf(IsInitVal)

INSTANCE FiniteSets
=============================================================================