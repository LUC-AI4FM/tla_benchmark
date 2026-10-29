---- MODULE IntDecrement ----
EXTENDS Naturals, Integers

VARIABLE x

Init == x = -1

Next == IF x > -3 THEN x' = x - 1 ELSE x' = x

Inv == x \in {-1, -2, -3}

Spec == Init /\ [][Next]_x
====