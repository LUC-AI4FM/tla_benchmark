------------------------------- MODULE TinyStateMachine -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS InitY
VARIABLES x, y

Init == /\ x = {}
        /\ y \in InitY

Next == \/ /\ x' \subseteq y'
            /\ y' = y
       \/ /\ x' = {1, 2, 3}
            /\ y' = y

FullSet == x = {1, 2, 3}

GainThree == x' = x \cup {3} /\ y' = y

Spec == Init /\ [][Next]_<<x,y>>

================================================================================