---- MODULE Github702 ----

EXTENDS Naturals, FiniteSets

CONSTANTS fizzbuzz

VARIABLES y, z

Init == /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == \/ y' = (y + 1) % 4
          /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>

MODULE x_unchanged

  EXTENDS Naturals, FiniteSets

  VARIABLE x

  CONSTANT c_x

  Init == x = c_x

  Next == \/ x' = x
            /\ UNCHANGED <<y, z>>

  Spec == Init /\ [][Next]_<<x, y, z>>

INSTANCE x_unchanged WITH x <- fizzbuzz, c_x <- fizzbuzz

====