MODULE TrivialStutter

EXTENDS Naturals, TLC

VARIABLE u1

Init == (u1 = TRUE)

Next == (u1' = u1)

Prop == \E u1' : (u1' = u1)

Spec == Init /\ [][Next]_{<<u1>>}