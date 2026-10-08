------------------------------- MODULE TinyStateMachine -------------------------------
EXTENDS TLC

CONSTANTS Y0
VARIABLES x, y

Init == /\ x = {}
        /\ y \in SUBSET {1, 2, 3}
        /\ y = Y0

Next ==
    \/ /\ x' \subseteq y
       /\ y' = y

FullSet == x = {1, 2, 3}

GainThree ==
    \/ /\ 3 \notin x
       /\ 3 \in x'

Spec ==
    /\ Init
    /\ [][Next]_<<x, y>>
    /\ TLCGet("States") = 8
    /\ TLCGet("FullSet") = 1
    /\ TLCGet("GainThree") = 3

=====================================================================================