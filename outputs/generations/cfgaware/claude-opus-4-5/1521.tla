---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

VARIABLE can

TypeOK == 
    /\ can \in [black: 0..MaxBeanCount, white: 0..MaxBeanCount]

TotalBeans == can.black + can.white

Init == 
    /\ can \in [black: 0..MaxBeanCount, white: 0..MaxBeanCount]
    /\ TotalBeans >= 1

RemoveTwoBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

RemoveTwoWhite ==
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @.black + 1, !.white = @.white - 2]

RemoveOneOfEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

Terminated == TotalBeans = 1

Termination ==
    /\ Terminated
    /\ UNCHANGED can

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneOfEach
    \/ Termination

Fairness == WF_can(Next)

Spec == Init /\ [][Next]_can /\ Fairness

MonotonicDecrease ==
    [][TotalBeans' < TotalBeans \/ (Terminated /\ UNCHANGED can)]_can

EventualTermination == <>(Terminated)

ParityInvariant ==
    can.white % 2 = can.white % 2

WhiteParityPreserved ==
    [][can'.white % 2 = can.white % 2]_can

FinalBeanHypothesis ==
    [](Terminated => 
        IF can.white % 2 = 1 
        THEN can.white = 1 /\ can.black = 0
        ELSE can.black = 1 /\ can.white = 0)

==========================================================================