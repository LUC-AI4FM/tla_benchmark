------------------------------- MODULE CoffeeCanBeanProblem -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxBeans

VARIABLES beans

Init == /\ beans \in [black: 0..MaxBeans, white: 0..MaxBeans]
        /\ (beans.black > 0 \/ beans.white > 0)

RemoveTwoBlack ==
    /\ beans.black >= 2
    /\ beans' = [beans EXCEPT !.black = beans.black - 2]

RemoveTwoWhite ==
    /\ beans.white >= 2
    /\ beans' = [beans EXCEPT !.white = beans.white - 2]

RemoveOneOfEach ==
    /\ beans.black > 0
    /\ beans.white > 0
    /\ beans' = [beans EXCEPT !.black = beans.black - 1, !.white = beans.white - 1]

Stutter ==
    /\ beans.black + beans.white = 1
    /\ beans' = beans

Next == \/ RemoveTwoBlack
        \/ RemoveTwoWhite
        \/ RemoveOneOfEach
        \/ Stutter

Spec == Init /\ [][Next]_<<beans>>

TypeInvariant == /\ beans.black \in 0..MaxBeans
                 /\ beans.white \in 0..MaxBeans

MonotonicDecrease == (beans'.black + beans'.white) <= (beans.black + beans.white)

ParityInvariant ==
    \/ (beans.white % 2 = 0)
    \/ (beans.black > 0 /\ beans.white = 1)

FinalBeanColor ==
    \/ (beans.black = 1 /\ beans.white = 0)
    \/ (beans.black = 0 /\ beans.white = 1)

WF_Stutter == WF(<<beans>>, Stutter)

THEOREM Spec => []TypeInvariant
THEOREM Spec => [](MonotonicDecrease)
THEOREM Spec /\ WF_Stutter => <>[](beans.black + beans.white = 1)
THEOREM Spec => [](ParityInvariant)
THEOREM Spec /\ WF_Stutter => <>(FinalBeanColor)

=============================================================================