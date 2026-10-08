------------------------------- MODULE Github702 --------------------------------

CONSTANTS fizzbuzz
VARIABLES y, z

Init == /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == \/ /\ y' = (y + 1) % 4
            /\ UNCHANGED <<fizzbuzz, z>>

Spec == Init /\ [][Next]_<<y, z>>

EXTENDS x_unchanged!Spec

=============================================================================