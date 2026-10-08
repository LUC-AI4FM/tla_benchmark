---- MODULE Github702 ----

CONSTANT fizzbuzz == 1

VARIABLES y, z

MODULE x_unchanged(x) ==
    VARIABLE x, y, z
    INIT /\ x \in {1, 2, 3}
         /\ y \in {1, 2, 3}
         /\ z \in {1, 2, 3}
    NEXT \/ UNCHANGED <<x, z>> /\ y' = (y + 1) % 4
    SPEC Spec == INIT /\ [][NEXT]_<<x, y, z>>
END MODULE

INSTANCE x_unchanged(fizzbuzz)

Spec == INSTANCE.Spec

====