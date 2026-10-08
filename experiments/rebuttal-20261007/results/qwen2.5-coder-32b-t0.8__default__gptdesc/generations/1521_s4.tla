------------------------------ MODULE CoffeeCanBean ------------------------------
EXTENDS TLC, Integers

CONSTANTS MaxBeans

VARIABLES state

Init == /\ state.black \in 0..MaxBeans
        /\ state.white \in 0..MaxBeans
        /\ state.total = state.black + state.white

TypeInvariant == /\ state.black \in 0..MaxBeans
                 /\ state.white \in 0..MaxBeans
                 /\ state.total = state.black + state.white

RemoveTwoBlack ==
    /\ state.black >= 2
    /\ '[state EXCEPT !.black = state.black - 2, !.total = state.total - 2]

RemoveTwoWhite ==
    /\ state.white >= 2
    /\ '[state EXCEPT !.white = state.white - 2, !.total = state.total - 2]

RemoveOneOfEach ==
    /\ state.black >= 1
    /\ state.white >= 1
    /\ '[state EXCEPT !.black = state.black - 1, !.white = state.white - 1, !.total = state.total - 2]

Stutter ==
    /\ state.total = 1

Next == \/ RemoveTwoBlack
        \/ RemoveTwoWhite
        \/ RemoveOneOfEach
        \/ Stutter

Spec == Init /\ [][Next]_<<state>>

Termination == <>(state.total = 1)

ParityInvariant == (state.white % 2) = (state.total % 2)

FinalColor ==
    /\ state.total = 1
    /\ (EXCEPT WHEN state.white % 2 = 0 THEN state.black = 1 ELSE state.white = 1)

SpecWithProperties == Spec /\ [][ParityInvariant]_<<state>> /\ WF_<<state>>(Next) /\ Termination /\ <>[FinalColor]_<<state>>
============================