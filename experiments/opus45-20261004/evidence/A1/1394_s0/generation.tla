---- MODULE Github702 ----
EXTENDS Integers

VARIABLES y, z

fizzbuzz == 42

---- MODULE x_unchanged ----
VARIABLE x
VARIABLES y, z

Init == /\ x \in {1, 2, 3}
        /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == /\ y' = y + 1
        /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>
====