---------------------------- MODULE Github715 ----------------------------
EXTENDS Booleans

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

SpecVar == x

Prop == []x

Prop2 == x = TRUE

Prop3 == TRUE

==========================================================================