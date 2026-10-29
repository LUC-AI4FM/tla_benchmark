---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

vars == << can >>

\* The set of all possible can states, with each color bounded by MaxBeanCount
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Total number of beans currently in the can
BeanCount == can.black + can.white

\* The can always holds a well-typed record of bean counts
TypeInvariant == can \in Can

\* Start with between 1 and MaxBeanCount beans in total
Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Pick two black beans: throw both away, put one black bean back
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Pick two white beans: throw both away, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Pick one bean of each color: throw away the black one, put the white one back
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean remains: the process terminates (stuttering)
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

\* Every step that changes the can strictly decreases the total number of beans
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* Eventually the process reaches the terminating state (one bean left)
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