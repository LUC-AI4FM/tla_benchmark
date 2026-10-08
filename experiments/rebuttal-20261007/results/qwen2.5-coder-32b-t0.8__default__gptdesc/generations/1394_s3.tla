-------------------- MODULE Github702 --------------------
EXTENDS Integers, FiniteSets

CONSTANTS fizzbuzz

VARIABLES y, z

Init == /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == \/ /\ y' = (y + 1) % 4
           /\ UNCHANGED <<x, z>>
          \/ /\ y' = y
           /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>


-------------------- MODULE x_unchanged --------------------
EXTENDS Integers, FiniteSets

VARIABLES x, y, z

Init == /\ x \in {1, 2, 3}
        /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == \/ /\ y' = (y + 1) % 4
           /\ UNCHANGED <<x, z>>
          \/ /\ y' = y
           /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>
===============================================