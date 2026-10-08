---- MODULE Github702 ----

EXTENDS Naturals, TLC

CONSTANTS fizzbuzz

VARIABLES y, z

MODULE x_unchanged(x) ==
    VARIABLES x, y, z
    INIT <<x, y, z>> \in {1, 2, 3}^3
    NEXT \/ /\ y' = y + 1
             /\ UNCHANGED <<x, z>>
         \/ /\ y' = y
             /\ UNCHANGED <<x, z>>
    SPEC Init /\ [][Next]_<<x, y, z>>

INSTANCE x_unchanged WITH x <- fizzbuzz

====