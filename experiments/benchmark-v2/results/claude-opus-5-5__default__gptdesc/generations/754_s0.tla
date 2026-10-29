---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

\* The set of all possible cans
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Total number of beans in the can
BeanCount == can.black + can.white

\* Initialize the can with a nonzero number of beans, bounded by MaxBeanCount
Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Pick two black beans: throw both away, put one black bean back in
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Pick two white beans: throw both away, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Pick one bean of each color: put the white bean back, throw the black away
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean remains: stutter
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* The total number of beans strictly decreases on every non-stuttering step
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* Eventually only one bean remains
EventuallyTerminates == <>(ENABLED Termination)

\* The parity of the number of white beans is preserved
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* The final bean is black iff the initial number of white beans is even
TerminationHypothesis ==
    /\ (can.white % 2 = 0) => <>(can.black = 1 /\ can.white = 0)
    /\ (can.white % 2 = 1) => <>(can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventuallyTerminates
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis
=============================================================================