------------------------------- MODULE CoffeeCan -------------------------------

CONSTANTS MaxBeanCount

VARIABLE can

(* --algorithm CoffeeCan
variables can = [black \in 0..MaxBeanCount, white \in 0..MaxBeanCount];

begin
    Init:
        with b \in 1..MaxBeanCount,
             w \in 0..(MaxBeanCount - b)
        do
            can := [black |-> b, white |-> w];
    
    Next ==
        \/ /\ can.black >= 2
           /\ can' = [can EXCEPT !.black = can.black - 1]
        \/ /\ can.white >= 2
           /\ can' = [can EXCEPT !.white = can.white - 1, !.black = can.black + 1]
        \/ /\ can.black >= 1
           /\ can.white >= 1
           /\ can' = [can EXCEPT !.black = can.black - 1]

    Termination ==
        \A c \in SUBSET (DOMAIN can) : #c = 1

    Spec ==
        Init /\ [][Next \/ Termination]_<<can>> /\ WF_next(Next)

    TypeInvariant ==
        /\ can.black \in 0..MaxBeanCount
        /\ can.white \in 0..MaxBeanCount
        /\ can.black + can.white \in 1..MaxBeanCount

    MonotonicDecrease ==
        \/ Termination
        \/ (can'.black + can'.white) < (can.black + can.white)

    LoopInvariant ==
        \/ Termination
        \/ can'.white % 2 = can.white % 2

    TerminationHypothesis ==
        \/ can.white % 2 = 0 /\ can.black = 1
        \/ can.white % 2 = 1 /\ can.white = 1
end algorithm *)

WF_next(next) == 
    \A S \in SUBSET (DOMAIN next) :
        \E T \in S : <S, T> \in [][next]_<<can>>

=============================================================================