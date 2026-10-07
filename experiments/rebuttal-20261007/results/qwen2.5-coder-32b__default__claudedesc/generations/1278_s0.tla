------------------------------- MODULE SimpleSystem -------------------------------

EXTENDS Naturals

CONSTANTS 

VARIABLES s

Init == s = 0

F(s_) == /\ s_ \in 0..9
         /\ s_ % 2 = 0

Next == \/ s' = s
        \/ F(s')

Spec == Init /\ [][Next]_s

=============================================================================