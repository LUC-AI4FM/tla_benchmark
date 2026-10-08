------------------------------- MODULE CoffeeCan -------------------------------

EXTENDS Integers, TLC

CONSTANTS MaxBeanCount

VARIABLES beans

Init == /\ beans.black \in 0..MaxBeanCount
        /\ beans.white \in 0..MaxBeanCount
        /\ (beans.black + beans.white) > 1

RemoveTwoBlack ==
    /\ beans.black >= 2
    /\ \/ beans.black' = beans.black - 2
       /\ beans.white' = beans.white
       /\ beans.black + beans.white > 1

RemoveTwoWhite ==
    /\ beans.white >= 2
    /\ \/ beans.black' = beans.black
       /\ beans.white' = beans.white - 2
       /\ beans.black + beans.white > 1

RemoveOneOfEach ==
    /\ beans.black >= 1
    /\ beans.white >= 1
    /\ \/ beans.black' = beans.black - 1
       /\ beans.white' = beans.white - 1
       /\ beans.black + beans.white > 1

TerminationStutter ==
    /\ beans.black + beans.white = 1
    /\ \/ beans.black' = beans.black
       /\ beans.white' = beans.white

Next == \/ RemoveTwoBlack
        \/ RemoveTwoWhite
        \/ RemoveOneOfEach
        \/ TerminationStutter

Spec ==
    /\ Init
    /\ [][Next]_<<beans>>
    /\ WF_next(<<beans>>)

TypeInvariant ==
    /\ beans.black \in 0..MaxBeanCount
    /\ beans.white \in 0..MaxBeanCount

MonotonicDecrease ==
    \/ beans.black' <= beans.black
    \/ beans.white' <= beans.white

ParityInvariant ==
    \/ (beans.white % 2 = 0) => (beans'.white % 2 = 0)
    \/ (beans.white % 2 = 1) => (beans'.white % 2 = 1)

TerminationProperty ==
    <>[]<> (beans.black + beans.white = 1)

FinalBeanColorHypothesis ==
    \/ (beans.white % 2 = 0) => \A h \in History: h.beans.black + h.beans.white > 1 => (beans'.black = 1)
    \/ (beans.white % 2 = 1) => \A h \in History: h.beans.black + h.beans.white > 1 => (beans'.white = 1)

=============================================================================