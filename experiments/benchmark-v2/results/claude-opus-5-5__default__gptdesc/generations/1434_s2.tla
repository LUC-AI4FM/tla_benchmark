---------------------------- MODULE DuplicateSuccessors ----------------------------
(***************************************************************************)
(* A very small transition system over a single variable x.  It is used   *)
(* to exercise TLC's next-state generation, and in particular how TLC     *)
(* treats duplicate successor states.                                     *)
(*                                                                         *)
(* TLC evaluates the next-state relation by exploring each disjunct of an *)
(* action separately.  Each disjunct that ends in a full assignment to x' *)
(* yields one successor state.  If two disjuncts assign the same value to *)
(* x', TLC generates the same successor twice.  The duplicate is counted  *)
(* in the "generated" statistic, but it is added only once to the set of  *)
(* distinct states.                                                       *)
(*                                                                         *)
(* The way disjuncts and assignments are arranged changes this behavior:  *)
(*                                                                         *)
(*  - A branch guarded by an obviously TRUE conjunct is explored like any *)
(*    other branch.  It can therefore produce a duplicate successor.      *)
(*                                                                         *)
(*  - A branch guarded by an obviously FALSE conjunct is pruned as soon   *)
(*    as the guard is evaluated.  It never produces a successor.          *)
(*                                                                         *)
(*  - Wrapping a formula in double negation (~~) stops TLC from treating  *)
(*    the inner x' = v as an assignment.  TLC must then evaluate it as a  *)
(*    Boolean condition, so x' has to be bound already, or TLC must       *)
(*    enumerate x' some other way.  This changes how many successors      *)
(*    TLC produces, and in which order.                                   *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
(* Initial state *)

Init == x = 42

-----------------------------------------------------------------------------
(* Candidate next-state actions *)

(* Two syntactically separate disjuncts that assign the same value.      *)
(* TLC generates the successor x = 5 twice, so there is one duplicate.   *)
NextDup ==
    /\ x = 42
    /\ \/ x' = 5
       \/ x' = 5

(* One branch is obviously TRUE and one is obviously FALSE.  The TRUE    *)
(* branch is explored and yields x = 5.  The FALSE branch is pruned and  *)
(* never yields x = 6.                                                   *)
NextTrueFalse ==
    /\ x = 42
    /\ \/ TRUE  /\ x' = 5
       \/ FALSE /\ x' = 6

(* An obviously TRUE disjunct sits next to an assignment.  Both branches *)
(* lead to the same successor, so TLC generates a duplicate.             *)
NextObviousTrue ==
    /\ x = 42
    /\ \/ x' = 5
       \/ TRUE /\ x' = 5

(* Double negation hides the second equality from TLC's assignment       *)
(* detection.  The first conjunct binds x' to 5.  The second conjunct is *)
(* then only a Boolean test, so TLC produces exactly one successor.      *)
NextDoubleNeg ==
    /\ x = 42
    /\ x' = 5
    /\ ~~(x' = 5)

(* A disjunction where one branch is a plain assignment and the other is *)
(* an assignment guarded by a double-negated condition on x' that comes  *)
(* after it.                                                             *)
NextDoubleNegDisj ==
    /\ x = 42
    /\ \/ x' = 5
       \/ x' = 5 /\ ~~(x' = 5)

(* Once x = 5 the system stutters.  Writing this as an explicit          *)
(* assignment keeps the next-state relation total on reachable states,   *)
(* so TLC reports no deadlock.                                           *)
Stay ==
    /\ x = 5
    /\ x' = x

Next ==
    \/ NextDup
    \/ NextTrueFalse
    \/ NextObviousTrue
    \/ NextDoubleNeg
    \/ NextDoubleNegDisj
    \/ Stay

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == x \in Nat

(* Only 42 and 5 are reachable.  The FALSE-guarded branch that sets      *)
(* x = 6 is never taken.                                                 *)
Inv == x \in {42, 5}

-----------------------------------------------------------------------------
(* Predicates *)

IsFive == x = 5

LeftInit == x # 42

-----------------------------------------------------------------------------
(* Liveness *)

(* Under weak fairness the system eventually leaves the initial state.   *)
EventuallyLeaves == <>LeftInit

(* Under weak fairness the system eventually reaches x = 5 and then      *)
(* stays there.                                                          *)
EventuallyAlwaysFive == <>[]IsFive

-----------------------------------------------------------------------------
(* TLC introspection *)

(* After model checking, TLC must report exactly two distinct states:    *)
(* x = 42 and x = 5.  Every duplicate successor generated by the actions *)
(* above is collapsed into one of these.  The number of generated states *)
(* must be at least the number of distinct states, because duplicates    *)
(* are counted when they are generated.                                  *)
PostCondition ==
    LET stats == TLCGet("stats")
    IN  /\ Assert(stats.distinct = 2,
                  <<"Unexpected number of distinct states", stats.distinct>>)
        /\ Assert(stats.generated >= stats.distinct,
                  <<"Generated fewer states than distinct", stats.generated>>)

(* Selected predicates must each describe exactly the expected number of *)
(* possible states within the reachable domain.                          *)
PredicateCounts ==
    LET Reach == {42, 5}
    IN  /\ Assert(Cardinality({v \in Reach : v = 5})  = 1, "IsFive count")
        /\ Assert(Cardinality({v \in Reach : v # 42}) = 1, "LeftInit count")
        /\ Assert(Cardinality({v \in Reach : v \in {42, 5}}) = 2, "Inv count")

Cardinality(S) == IF S = {} THEN 0 ELSE
    LET f[T \in SUBSET S] == IF T = {} THEN 0
                             ELSE 1 + f[T \ {CHOOSE t \in T : TRUE}]
    IN  f[S]

=============================================================================