---------------------------- MODULE CoffeeCan ----------------------------

EXTENDS Naturals

CONSTANT MaxBeanCount

VARIABLE can

TypeInvariant ==
    /\ can.black \in 0..MaxBeanCount
    /\ can.white \in 0..MaxBeanCount
    /\ can.black + can.white >= 0
    /\ can.black + can.white <= MaxBeanCount

Init ==
    \E b \in 0..MaxBeanCount, w \in 0..MaxBeanCount :
        /\ b + w >= 1
        /\ b + w <= MaxBeanCount
        /\ can = [black |-> b, white |-> w]

PickTwoBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = can.black - 1]

PickTwoWhite ==
    /\ can.white >= 2
    /\ can' = [black |-> can.black + 1, white |-> can.white - 2]

PickOneOfEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = can.black - 1]

Termination ==
    /\ can.black + can.white = 1
    /\ UNCHANGED can

Next ==
    \/ PickTwoBlack
    \/ PickTwoWhite
    \/ PickOneOfEach
    \/ Termination

Spec == Init /\ [][Next]_can /\ WF_can(Next)

TotalBeans == can.black + can.white

MonotonicDecrease ==
    [][TotalBeans' < TotalBeans \/ can' = can]_can

LoopInvariant ==
    [][(can'.white % 2) = (can.white % 2)]_can

TerminationHypothesis ==
    \A initWhiteParity \in {0, 1} :
        (can.white % 2 = initWhiteParity) =>
            <>(IF initWhiteParity = 0
               THEN can = [black |-> 1, white |-> 0]
               ELSE can = [black |-> 0, white |-> 1])

==========================================================================