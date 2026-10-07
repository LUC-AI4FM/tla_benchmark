MODULE B
VARIABLES x

Switch == \lnot x

A == x' = Switch
B == x' = Switch

Next == A \/ B

Init == x = FALSE

Spec == Init /\ [][Next]_x