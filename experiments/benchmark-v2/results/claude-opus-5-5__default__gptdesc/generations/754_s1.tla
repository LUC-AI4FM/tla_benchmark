---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

\* The set of all possible can states
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Total number of beans in the can
BeanCount == can.black + can.white

-----------------------------------------------------------------------------
\* Type invariant
TypeInvariant == can \in Can

-----------------------------------------------------------------------------
\* Initial state: any can with at least one bean and at most MaxBeanCount beans
Init ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* Two black beans picked: both removed, one black bean put back
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans picked: both removed, one black bean added
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One black and one white picked: white removed, black put back
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.white = @ - 1]

\* Only one bean left: stutter forever
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
\* Properties

\* Every non-stuttering step strictly decreases the number of beans
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* Eventually only one bean remains (termination state reached)
EventuallyTerminates == <>(ENABLED Termination)

\* The parity of the number of white beans is preserved by every step
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* The final bean is black iff the initial number of white beans is even
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