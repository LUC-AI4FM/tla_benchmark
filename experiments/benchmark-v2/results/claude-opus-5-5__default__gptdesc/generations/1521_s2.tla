---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

\* The set of all possible can states
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Total number of beans currently in the can
BeanCount == can.black + can.white

-----------------------------------------------------------------------------
\* Initial state: some number of black and white beans, at least one bean,
\* total bounded by MaxBeanCount
Init ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* Remove two black beans, put one black bean back
PickSameColorBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Remove two white beans, put one black bean in
PickSameColorWhite ==
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Remove one black and one white bean, put the white bean back
PickDifferentColor ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Termination: exactly one bean remains; stutter
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
\* Safety: type invariant
TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* Safety: every non-stuttering step strictly decreases the bean count
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* Liveness: eventually only one bean remains
EventuallyTerminates == <>(ENABLED Termination)

\* Loop invariant: the parity of the number of white beans never changes
LoopInvariant ==
    [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* Hypothesis: if the initial number of white beans is even, the final bean
\* is black; if it is odd, the final bean is white
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