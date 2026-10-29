---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

BeanCount == can.black + can.white

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

TypeInvariant ==
    /\ can \in Can
    /\ can.black >= 0
    /\ can.white >= 0
    /\ BeanCount >= 1
    /\ BeanCount <= MaxBeanCount

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Two black beans picked: both discarded, one black bean added
PickSameColorBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans picked: both discarded, one black bean added
PickSameColorWhite ==
    /\ can.white >= 2
    /\ can' = [black |-> can.black + 1, white |-> can.white - 2]

\* One black and one white picked: black discarded, white returned
PickDifferentColor ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorBlack
    \/ PickSameColorWhite
    \/ PickDifferentColor
    \/ Termination

BeanActions ==
    PickSameColorBlack \/ PickSameColorWhite \/ PickDifferentColor

Spec == Init /\ [][Next]_vars /\ WF_vars(BeanActions)

-----------------------------------------------------------------------------
\* Correctness properties

NonNegative == can.black >= 0 /\ can.white >= 0

\* Parity of the white bean count never changes
LoopInvariant ==
    [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

\* Each bean operation removes exactly one bean
MonotonicDecrease ==
    [][BeanActions => (can'.black + can'.white = BeanCount - 1)]_vars

\* The process eventually ends with exactly one bean
EventuallyTerminates == <>(BeanCount = 1)

\* The final bean is white iff the initial number of white beans is odd
FinalBeanDetermined ==
    \A w \in 0..MaxBeanCount :
        (can.white = w) =>
            <>( /\ BeanCount = 1
                /\ (can.white = 1 <=> w % 2 = 1)
                /\ (can.black = 1 <=> w % 2 = 0) )

THEOREM Spec => []TypeInvariant
THEOREM Spec => LoopInvariant /\ MonotonicDecrease
THEOREM Spec => EventuallyTerminates /\ FinalBeanDetermined
=============================================================================