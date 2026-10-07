------------------------------- MODULE CoffeeCan -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxBeanCount

VARIABLES can

Init == /\ can \in [black: 0..MaxBeanCount, white: 0..MaxBeanCount]
        /\ can.black + can.white >= 1
        /\ can.black + can.white <= MaxBeanCount

Next ==
    \/ /\ can.black >= 2
       /\ can' = [can EXCEPT !.black = can.black - 1]
    \/ /\ can.white >= 2
       /\ can' = [can EXCEPT !.white = can.white - 1, !.black = can.black + 1]
    \/ /\ can.black >= 1
       /\ can.white >= 1
       /\ can' = [can EXCEPT !.black = can.black - 1]
    \/ /\ can.black + can.white = 1
       /\ can' = can

Termination == can.black + can.white = 1

Spec ==
    /\ Init
    /\ [][Next]_<<can>>
    /\ WF_next(Next)

TypeInvariant ==
    /\ can.black \in 0..MaxBeanCount
    /\ can.white \in 0..MaxBeanCount
    /\ can.black + can.white >= 1
    /\ can.black + can.white <= MaxBeanCount

MonotonicDecrease ==
    \/ can'.black + can'.white < can.black + can.white
    \/ Termination

LoopInvariant ==
    (can.black' + can.white') % 2 = (can.black + can.white) % 2

TerminationHypothesis ==
    /\ can.white % 2 = 0 => can.black = 1
    /\ can.white % 2 = 1 => can.white = 1

=============================================================================