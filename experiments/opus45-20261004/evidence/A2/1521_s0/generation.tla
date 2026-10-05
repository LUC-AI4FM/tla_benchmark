---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeanCount

VARIABLES can, initialWhiteParity

vars == <<can, initialWhiteParity>>

TypeInvariant ==
    /\ can.black \in 0..MaxBeanCount
    /\ can.white \in 0..MaxBeanCount
    /\ can.black + can.white >= 0
    /\ can.black + can.white <= MaxBeanCount
    /\ initialWhiteParity \in {0, 1}

TotalBeans == can.black + can.white

Init ==
    /\ can \in [black : 0..MaxBeanCount, white : 0..MaxBeanCount]
    /\ can.black + can.white >= 1
    /\ can.black + can.white <= MaxBeanCount
    /\ initialWhiteParity = can.white % 2

PickTwoBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = can.black - 1]
    /\ initialWhiteParity' = initialWhiteParity

PickTwoWhite ==
    /\ can.white >= 2
    /\ can' = [black |-> can.black + 1, white |-> can.white - 2]
    /\ initialWhiteParity' = initialWhiteParity

PickOneEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = can.black - 1]
    /\ initialWhiteParity' = initialWhiteParity

Termination ==
    /\ TotalBeans = 1
    /\ UNCHANGED vars

Next ==
    \/ PickTwoBlack
    \/ PickTwoWhite
    \/ PickOneEach
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MonotonicDecrease ==
    [][TotalBeans' < TotalBeans \/ TotalBeans = 1]_vars

LoopInvariant ==
    [](can.white % 2 = initialWhiteParity)

TerminationHypothesis ==
    <>(
        /\ TotalBeans = 1
        /\ (initialWhiteParity = 0 => can.black = 1)
        /\ (initialWhiteParity = 1 => can.white = 1)
    )

==========================================================================