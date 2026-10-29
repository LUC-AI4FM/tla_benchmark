---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

vars == << can >>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant == can \in Can

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Two black beans: remove both, put one black back.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans: remove both, put one black in.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One of each color: put the white back, discard the black.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean left: stutter.
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
\* Properties

\* Every non-stuttering step strictly decreases the number of beans.
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* Eventually only one bean remains.
EventuallyTerminates == <>(ENABLED Termination)

\* The parity of the number of white beans never changes.
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* The last bean is black iff the initial number of white beans is even.
TerminationHypothesis ==
    \A w \in 0..MaxBeanCount :
        (can.white = w) =>
            <>(/\ BeanCount = 1
               /\ ((can.black = 1) <=> (w % 2 = 0)))

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventuallyTerminates
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis
=============================================================================