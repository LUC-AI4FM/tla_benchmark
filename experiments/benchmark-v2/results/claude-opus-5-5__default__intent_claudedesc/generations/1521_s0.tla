---------------------------- MODULE CoffeeCan ----------------------------
(***************************************************************************)
(* The Coffee Can problem (Dijkstra & Scholten, described in Gries's       *)
(* "The Science of Programming").                                          *)
(*                                                                         *)
(* A coffee can holds some black and white beans. Repeatedly draw two      *)
(* beans:                                                                  *)
(*   - both black   : discard both, return one black bean                  *)
(*   - both white   : discard both, add one black bean                     *)
(*   - different    : return the white bean, discard the black bean        *)
(* Each round reduces the bean count by exactly one. The process ends when *)
(* a single bean remains. The parity of the white bean count is invariant, *)
(* so the final bean's color is determined by the initial white count.     *)
(*                                                                         *)
(* Model-check with, for example, MaxBeanCount = 100.                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCountAssumption == MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Two black beans drawn: discard both, return one black bean.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans drawn: discard both, add one black bean.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One of each drawn: return the white bean, discard the black bean.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean remains: the process has terminated (stutter).
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
(* Properties *)

\* 1. Every (non-stuttering) step strictly decreases the number of beans.
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* 2. The parity of the white bean count is preserved on every step.
LoopInvariant ==
    [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* 3. The process eventually terminates with exactly one bean.
EventuallyTerminates == <>(BeanCount = 1)

\* Once terminated, it stays terminated.
TerminationIsStable == [](BeanCount = 1 => [](BeanCount = 1))

\* 4. The final bean's color is determined by the initial white count
\*    (this formula is evaluated with respect to the initial state).
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>[](can.black = 1 /\ can.white = 0)
    ELSE <>[](can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => LoopInvariant
THEOREM Spec => EventuallyTerminates
THEOREM Spec => TerminationHypothesis

(***************************************************************************)
(* Suggested TLC configuration (CoffeeCan.cfg):                            *)
(*   CONSTANT MaxBeanCount = 100                                           *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeInvariant                                               *)
(*   PROPERTIES MonotonicDecrease LoopInvariant                            *)
(*              EventuallyTerminates TerminationIsStable                   *)
(*              TerminationHypothesis                                      *)
(***************************************************************************)
=============================================================================