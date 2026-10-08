MODULE Trivial
VARIABLES u1

vars == <<u1>>

Init == (u1 = TRUE)

Next == (u1' = u1)

Prop == \E u' : Next

Spec == Init /\ [][Next]_vars