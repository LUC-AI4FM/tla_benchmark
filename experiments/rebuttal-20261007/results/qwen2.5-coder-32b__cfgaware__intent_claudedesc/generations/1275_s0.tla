------------------------------- MODULE InitializationConstraint -------------------------------

VARIABLES x

CONSTANTS Init, Spec, Inv, Next, TypeOK

Init == \/ x = 0 /\ x < 1

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Inv == x < 1

TypeOK == x \in {0}

=============================================================================