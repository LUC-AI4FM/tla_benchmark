------------------------------- MODULE SmallStateSystem -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Data

VARIABLES state

Init == state = {}

Next == /\ state \in SUBSET Data
        /\ \/ CHOOSE x \in Data \ state : state' = state \cup {x}

Spec == Init /\ [][Next]_<<state>>

=====================================================================================