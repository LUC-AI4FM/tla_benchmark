MODULE x_unchanged
EXTENDS Naturals

CONSTANTS X

VARIABLES y, z

Init ==
  /\ y \in {1,2,3}
  /\ z \in {1,2,3}
  /\ X \in {1,2,3}

Next ==
  /\ y' = y + 1
  /\ UNCHANGED <<X, z>>

Spec == Init /\ [][Next]_<<X, y, z>>


MODULE Github702
EXTENDS x_unchanged

CONSTANTS fizzbuzz == 1   \* constant-valued operator

VARIABLES y, z

INSTANCE x_unchanged WITH X <- fizzbuzz

Spec == x_unchanged.Spec