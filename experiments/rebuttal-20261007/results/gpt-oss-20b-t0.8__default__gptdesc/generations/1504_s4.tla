MODULE Trivial

VARIABLES u1

Init == u1 = TRUE

Next == u1' = u1

Prop == ENABLED Next

Spec == Init /\ [][Next]_u1