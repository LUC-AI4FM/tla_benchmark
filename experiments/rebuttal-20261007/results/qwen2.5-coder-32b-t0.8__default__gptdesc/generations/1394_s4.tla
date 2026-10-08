------------------------------ MODULE Github702 ------------------------------

CONSTANTS fizzbuzz

VARIABLES y, z

Init == /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == \/ /\ y' = (y + 1) % 4
          /\ UNCHANGED <<x, z>>
          \/ /\ x' = fizzbuzz
          /\ UNCHANGED <<y, z>>

Spec == Init /\ [][Next]_<<x, y, z>>

MODULE ==============================================================