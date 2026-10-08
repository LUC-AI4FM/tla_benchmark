------------------------------- MODULE SmallTemporalModel ------------------------------

EXTENDS Naturals

CONSTANTS 
    Next

VARIABLES 
    s

Init == s = 23

Next ==
    \E val \in {0, 1} : /\ s' = val
                        /\ s' > 0

Inv == s # 0

Spec == Init /\ [][Next]_<<s>>

=============================================================================