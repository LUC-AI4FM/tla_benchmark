---------------------------- MODULE spec ----------------------------

VARIABLE x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

XisTrue == x = TRUE

XisFalse == x = FALSE

Prop == x = TRUE \/ x = FALSE

=============================================================================