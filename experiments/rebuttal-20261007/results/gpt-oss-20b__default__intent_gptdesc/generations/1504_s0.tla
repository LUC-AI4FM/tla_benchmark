MODULE StutteringBool
EXTENDS Naturals

VARIABLE b

Init == b = TRUE

Next == b' = b

Spec == Init /\ [][Next]_<<b>>

NoDeadlock == [] (EXISTS b' : Next)

InvariantTrue == [] (b = TRUE)