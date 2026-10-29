------------------------------ MODULE CoffeeCan ------------------------------
(***************************************************************************)
(* The coffee can problem.  A can initially holds a finite, nonzero        *)
(* number of beans, each black or white.  While at least two beans remain, *)
(* two beans are removed nondeterministically:                             *)
(*   - same color      : both discarded, one black bean put in;            *)
(*   - different color : the white bean is returned, the black discarded.  *)
(* Each step removes exactly one bean, so the process terminates with one  *)
(* bean left.  The parity of the white count never changes, so the final   *)
(* bean is white iff the initial number of white beans is odd.             *)
(*                                                                         *)
(* Fairness: weak fairness on Next rules out infinite deferral of an       *)
(* enabled transition (infinite stuttering).  Initial totals are bounded   *)
(* by the finite constant MaxBeanCount, so termination is meaningful.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Two black beans removed: discard both, put in one black.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans removed: discard both, put in one black.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One black and one white removed: return white, discard black.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Terminal condition: one bean left, nothing more can happen.
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorBlack
    \/ PickSameColorWhite
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_can /\ WF_can(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Safety: every non-stuttering step decreases the bean count by exactly one.
MonotonicDecrease == [][BeanCount' = BeanCount - 1]_BeanCount

\* Liveness: the process eventually reaches a state with exactly one bean.
EventuallyTerminates == <>(BeanCount = 1)

\* Invariant: parity of the number of white beans is preserved by every step.
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_can

\* Final-state characterization, determined by initial white parity.
TerminationHypothesis ==
    IF can.white % 2 = 0
        THEN <>(can.black = 1 /\ can.white = 0)
        ELSE <>(can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventuallyTerminates
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis
=============================================================================