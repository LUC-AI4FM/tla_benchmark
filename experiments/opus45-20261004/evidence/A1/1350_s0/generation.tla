---------------------------- MODULE Specification ----------------------------

VARIABLE x

Init == x = 1

Next == 
    IF x < 5 
    THEN x' = x + 1
    ELSE x' = x

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Liveness == (x = 1) ~> [](x = 5)

=============================================================================