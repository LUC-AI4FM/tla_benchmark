---- MODULE ConstantZero ----

VARIABLES x

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == x = 0

Liveness == []<>(x = 0)

====