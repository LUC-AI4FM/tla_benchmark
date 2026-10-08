---- MODULE StateMachine ----
EXTENDS TLC

CONSTANTS Domain

VARIABLES x, y

Init == /\ x = {}
        /\ y \in SUBSET Domain
        /\ Cardinality(y) >= 2

Next == /\ x' \subseteq y'
        /\ y' = y
        /\ (x' = {1, 2, 3} => FullSet)
        /\ (\E a \notin x : a \in x' => GainThree)

FullSet == x = {1, 2, 3}

GainThree == 3 \in x

Spec == Init /\ [][Next]_<<x, y>>

====