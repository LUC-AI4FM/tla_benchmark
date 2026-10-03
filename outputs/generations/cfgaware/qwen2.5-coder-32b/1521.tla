------------------------------- MODULE CoffeeCanBeanProblem -------------------------------

CONSTANTS MaxBeans \* Maximum number of beans in the can

VARIABLES state \* State record with fields black and white

vars == <<state>>

Init == /\ state.black \in 0..MaxBeans
        /\ state.white \in 0..MaxBeans
        /\ (state.black + state.white) > 0

TypeInvariant ==
    /\ state.black \in 0..MaxBeans
    /\ state.white \in 0..MaxBeans

MonotonicDecrease ==
    \/ (/\ PC = "RemoveTwoBlack"
        /\ 'old.state.black >= 2
        /\ state.black = 'old.state.black - 2)
    \/ (/\ PC = "RemoveTwoWhite"
        /\ 'old.state.white >= 2
        /\ state.white = 'old.state.white - 2)
    \/ (/\ PC = "RemoveOneOfEach"
        /\ 'old.state.black >= 1
        /\ 'old.state.white >= 1
        /\ state.black = 'old.state.black - 1
        /\ state.white = 'old.state.white - 1)

ParityInvariant ==
    \/ (state.black + state.white) = 0
    \/ (state.black + state.white) = 1
    \/ (state.white % 2 = 'old.state.white % 2)

Next ==
    \/ /\ PC = "RemoveTwoBlack"
       /\ state.black >= 2
       /\ state' = [black |-> state.black - 2, white |-> state.white]
    \/ /\ PC = "RemoveTwoWhite"
       /\ state.white >= 2
       /\ state' = [black |-> state.black, white |-> state.white - 2]
    \/ /\ PC = "RemoveOneOfEach"
       /\ state.black >= 1
       /\ state.white >= 1
       /\ state' = [black |-> state.black - 1, white |-> state.white - 1]
    \/ /\ PC = "Stutter"
       /\ (state.black + state.white) = 1
       /\ state' = state

Spec ==
    Init /\ [][Next]_<<state>> /\ WF_next(<<state>>)

Termination ==
    <>(state.black + state.white) = 1

FinalColor ==
    \/ (/\ (state.black + state.white) = 1
        /\ state.white = 0)
    \/ (/\ (state.black + state.white) = 1
        /\ state.black = 0)

=============================================================================