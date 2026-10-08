---- MODULE EvenRange ----

VARIABLE s

F(x) == x \in {0, 2, 4, 6, 8}

Init == s = 0

Spec == Init /\ []([F(s')]_s)

====