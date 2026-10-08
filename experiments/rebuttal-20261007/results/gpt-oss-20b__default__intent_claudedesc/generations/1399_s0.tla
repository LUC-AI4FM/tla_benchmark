------------------------------ MODULE Toggle ------------------------------
EXTENDS Naturals

VARIABLE x

Init == x = TRUE

Next == x' = NOT x

Spec == Init /\ [][Next]_x

AlwaysTrue == [](x = TRUE)

StateTrue == (x = TRUE)

TriviallyTrue == TRUE

VarProperty == x
=============================================================================