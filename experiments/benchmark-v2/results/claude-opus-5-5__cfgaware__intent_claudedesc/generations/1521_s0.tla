---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount
ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant == can \in Can

Init ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* Two black beans drawn: both discarded, one black returned.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans drawn: both discarded, one black added.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One of each color drawn: white returned, black discarded.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean remains: the process halts.
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Every (non-stuttering) step strictly decreases the number of beans.
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* The process eventually reaches a single bean.
EventuallyTerminates == <>(ENABLED Termination)

\* The parity of the white bean count is preserved by every step.
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* The final bean's color is determined by the initial white bean parity.
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

=============================================================================