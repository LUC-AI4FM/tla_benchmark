------------------------------ MODULE SmallTemporalSystem ------------------------------
EXTENDS Naturals

CONSTANTS 
    F

VARIABLES s

Init == s = 0

F(var) == (var \in 0..9) /\ (var % 2 = 0)

Next == TRUE

Spec == Init /\ [][F(s')]_<<s>>

================================================================================