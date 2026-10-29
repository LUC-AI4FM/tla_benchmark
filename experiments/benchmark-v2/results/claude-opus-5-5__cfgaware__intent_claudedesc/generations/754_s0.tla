---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Two black beans picked: discard both, add one black bean
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans picked: discard both, add one black bean
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One of each picked: discard the black bean, return the white bean
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Process is finished; stutter to avoid spurious deadlock
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorBlack
    \/ PickSameColorWhite
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Every non-stuttering step strictly decreases the bean count
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* The process eventually reaches a state with exactly one bean
EventuallyTerminates == <>(ENABLED Termination)

\* The parity of the white bean count is preserved by every step
LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_vars

\* The final bean's color is determined by the parity of the initial white count
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

=============================================================================