------------------------------- MODULE SmallTemporalModel -------------------------------
EXTENDS Naturals

CONSTANTS Next

VARIABLES s

Init == s = 23

Next == /\ s' \in {0, 1}
        /\ s' > 0

Inv == s # 0

Spec ==
    /\ Init
    /\ [][Next]_s
    /\ [](Inv)

=============================================================================