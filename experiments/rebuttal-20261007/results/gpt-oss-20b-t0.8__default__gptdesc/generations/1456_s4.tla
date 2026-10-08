MODULE TinyStateMachine
EXTENDS TLC

VARIABLES x, y

DOMAIN == {1,2,3}

Init == /\ x \in SUBSET DOMAIN
       /\ y \in SUBSET DOMAIN

Next == /\ y' = y
        /\ x' \subseteq y'
        /\ x' \in SUBSET DOMAIN
        /\ y' \in SUBSET DOMAIN

FullSet   == (x = DOMAIN)
GainThree == 3 \in x' /\ 3 \notin x

Spec == Init /\ [][Next]_<<x, y>>

ASSERT (TLCGet("FullSet") = 0)
ASSERT (TLCGet("GainThree") = 0)