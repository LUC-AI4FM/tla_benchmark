------------------------------- MODULE Github702 -------------------------------
EXTENDS Integers, TLC

CONSTANTS fizzbuzz
VARIABLES y, z

fizzbuzz == 1

MODULE x_unchanged(x)
    VARIABLES x, y, z
    Init == /\ x \in {1, 2, 3}
           /\ y \in {1, 2, 3}
           /\ z \in {1, 2, 3}
    Next == \/ /\ UNCHANGED <<x, z>>
              /\ y' = (y + 1) % 4
    Spec == Init /\ [][Next]_<<x, y, z>>
END MODULE

INSTANCE x_unchanged(fizzbuzz)

Spec == INSTANCE.Spec

=============================================================================