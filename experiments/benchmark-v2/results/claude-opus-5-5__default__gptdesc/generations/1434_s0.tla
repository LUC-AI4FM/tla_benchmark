--------------------------- MODULE DuplicateStates ---------------------------
(***************************************************************************)
(* A very small transition system over a single variable x.  It exists to  *)
(* exercise TLC's next-state generation, in particular how TLC handles     *)
(* duplicate successor states.                                             *)
(*                                                                         *)
(* TLC explores the disjuncts of an action from left to right. Each time  *)
(* a disjunct fully determines the primed variables, TLC produces one      *)
(* successor state. Syntactically different disjuncts can determine the   *)
(* same assignment, for example x' = 5 \/ x' = 5. TLC then generates the  *)
(* same successor twice. The fingerprint set later folds these into one   *)
(* distinct state, but the "generated states" count includes both.        *)
(*                                                                         *)
(* Several arrangements are modelled below:                                *)
(*   - Plain duplicated disjuncts.                                         *)
(*   - A branch that is guarded by an obviously TRUE conjunct. TLC still  *)
(*     evaluates it and produces the assignment.                           *)
(*   - A branch that is guarded by an obviously FALSE conjunct. TLC prunes *)
(*     it before any assignment, so it never contributes a successor.      *)
(*   - A double negation ~~(x' = 5). TLC cannot treat a negated formula as *)
(*     an assignment, so x' = 5 under ~~ acts as a test, not a generator.  *)
(*     This changes evaluation behaviour: it only filters states in which  *)
(*     x' is already bound, and it does not create a new successor.        *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLE x

vars == << x >>

Init == x = 42

(* Two syntactically identical disjuncts: TLC generates x' = 5 twice.      *)
NextDup ==
    \/ x' = 5
    \/ x' = 5

(* Obviously-true guard: the branch is taken and yields x' = 5 again.      *)
(* Obviously-false guard: the branch is pruned, so x' = 6 never occurs.    *)
NextTrueFalse ==
    \/ TRUE  /\ x' = 5
    \/ FALSE /\ x' = 6

(* Double negation: the second disjunct is not an assignment. It is only  *)
(* evaluated once x' has been bound by the conjunct that precedes it, so  *)
(* it acts as a test and adds no new successor.                           *)
NextDoubleNeg ==
    \/ x' = 5
    \/ x' = 5 /\ ~~(x' = 5)

(* Once x = 5, the system stutters so that it does not deadlock.          *)
Done == x = 5 /\ UNCHANGED x

Next ==
    \/ x = 42 /\ NextDup
    \/ x = 42 /\ NextTrueFalse
    \/ x = 42 /\ NextDoubleNeg
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: only 42 and 5 are reachable. In particular, 6 never is.         *)
Inv == x \in {42, 5}

TypeOK == x \in Nat

(* Predicate identifying the state x = 5.                                  *)
IsFive == x = 5

(* Predicate for having left the initial state.                            *)
LeftInit == x # 42

(* Liveness: under weak fairness, the system eventually leaves the initial *)
(* state, and then stays at x = 5 forever.                                 *)
EventuallyLeaves == <>LeftInit
EventuallyFive   == <>[]IsFive

-----------------------------------------------------------------------------
(* TLC introspection. This checks the statistics that TLC reports for the  *)
(* selected predicates. Exactly two distinct states can exist (42 and 5),  *)
(* no matter how many duplicate successors were generated. The generated  *)
(* count is at least the distinct count. The check is meant to be used as *)
(* an invariant or as a POSTCONDITION.                                     *)
NumDistinct == TLCGet("stats").distinct
NumGenerated == TLCGet("stats").generated

StatsOK ==
    /\ NumDistinct <= Cardinality({42, 5})
    /\ NumGenerated >= NumDistinct
    /\ (IsFive \/ ~LeftInit)

Cardinality(S) ==
    LET CS[T \in SUBSET S] ==
            IF T = {} THEN 0 ELSE 1 + CS[T \ {CHOOSE e \in T : TRUE}]
    IN  CS[S]

THEOREM Spec => []Inv
=============================================================================