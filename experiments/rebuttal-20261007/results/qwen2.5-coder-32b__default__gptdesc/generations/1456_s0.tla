------------------------------- MODULE TinyStateMachine -------------------------------
EXTENDS TLC

CONSTANTS YInit

VARIABLES x, y

Init == /\ x = {}
        /\ y \in SUBSET {1, 2, 3}
        /\ y = YInit

Next ==
    \/ /\ x' \subseteq y'
       /\ y' = y
       /\ (x' = {1, 2, 3} => TLCGet("FullSet") = TLCGet("FullSet") + 1)
       /\ (x' = x \cup {3} => TLCGet("GainThree") = TLCGet("GainThree") + 1)

Spec == Init /\ [][Next]_<<x, y>>

FullSet == x = {1, 2, 3}
GainThree == 3 \notin x \/ 3 \in x'

=============================================================================