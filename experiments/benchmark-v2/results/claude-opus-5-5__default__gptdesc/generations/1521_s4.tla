---------------------------- MODULE CoffeeCan ----------------------------
(***************************************************************************)
(* The coffee can bean problem.                                            *)
(*                                                                         *)
(* A can holds some black and white beans. While more than one bean is     *)
(* left, we repeatedly remove two beans:                                   *)
(*   - two black beans: put one black bean back;                           *)
(*   - two white beans: put one black bean back;                           *)
(*   - one of each: put the white bean back.                               *)
(* Each step lowers the total bean count by one, so the process ends with  *)
(* exactly one bean. That bean is white exactly when the starting number   *)
(* of white beans is odd.                                                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCountAssumption == MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

-----------------------------------------------------------------------------
(* Type invariant *)
TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

-----------------------------------------------------------------------------
(* Initial state: at least one bean, at most MaxBeanCount beans *)
Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

(* Remove two black beans and put one black bean back *)
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Remove two white beans and put one black bean back *)
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

(* Remove one black and one white bean and put the white bean back *)
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Termination: exactly one bean remains, so the state stutters *)
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorBlack
    \/ PickSameColorWhite
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: every non-stuttering step lowers the total bean count *)
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

(* Liveness: the process eventually reaches a single bean *)
EventuallyTerminates == <>(ENABLED Termination)

(* Loop invariant: every step preserves the parity of the white beans *)
LoopInvariant ==
    [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

(* Hypothesis: an even starting white count leaves one black bean;      *)
(* an odd starting white count leaves one white bean.                   *)
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventuallyTerminates
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis
=============================================================================