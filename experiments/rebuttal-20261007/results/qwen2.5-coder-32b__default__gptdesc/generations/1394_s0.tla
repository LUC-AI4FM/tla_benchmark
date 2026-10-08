---- MODULE Github702 ----

EXTENDS Naturals, FiniteSets

CONSTANTS fizzbuzz

VARIABLES y, z

MODULE x_unchanged(x)
    VARIABLES x, y, z
    INIT <<x, y, z>> \in {1, 2, 3} \X {1, 2, 3} \X {1, 2, 3}
    NEXT \/ /\ y' = y + 1
             /\ UNCHANGED <<x, z>>
         \/ /\ x' = x
             /\ y' = y
             /\ z' = z
END MODULE

INSTANCE x_unchanged WITH x <- fizzbuzz

Init == INSTANCE.Init

Next == INSTANCE.Next

Spec == Init /\ [][Next]_<<fizzbuzz, y, z>>

====