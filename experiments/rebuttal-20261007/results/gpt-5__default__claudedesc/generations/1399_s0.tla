------------------------------ MODULE Github715 ------------------------------

EXTENDS TLC

CONSTANTS Dummy

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

Prop == [](x)

Prop2 == x = TRUE

Prop3 == TRUE

SpecVar == x

=============================================================================