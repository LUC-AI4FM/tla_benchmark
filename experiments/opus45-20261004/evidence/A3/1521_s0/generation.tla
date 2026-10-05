---------------------------- MODULE CoffeeCanBeans ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeans

VARIABLES beans

TypeOK ==
    /\ beans \in [black: 0..MaxBeans, white: 0..MaxBeans]

TotalBeans == beans.black + beans.white

Init ==
    /\ beans \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ TotalBeans >= 1

RemoveTwoBlack ==
    /\ beans.black >= 2
    /\ beans' = [beans EXCEPT !.black = @ - 1]

RemoveTwoWhite ==
    /\ beans.white >= 2
    /\ beans' = [beans EXCEPT !.white = @ - 1, !.black = @ + 1]

RemoveOneEach ==
    /\ beans.black >= 1
    /\ beans.white >= 1
    /\ beans' = [beans EXCEPT !.black = @ - 1]

Terminated ==
    /\ TotalBeans = 1
    /\ UNCHANGED beans

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneEach
    \/ Terminated

Spec == Init /\ [][Next]_beans /\ WF_beans(Next)

MonotonicDecrease ==
    [][TotalBeans' <= TotalBeans]_beans

EventualTermination ==
    <>(TotalBeans = 1)

WhiteParityInvariant ==
    [][beans'.white % 2 = beans.white % 2]_beans

FinalBeanHypothesis ==
    [](TotalBeans = 1 =>
        IF beans.white % 2 = 1
        THEN beans.white = 1 /\ beans.black = 0
        ELSE beans.white = 0 /\ beans.black = 1)

===============================================================================