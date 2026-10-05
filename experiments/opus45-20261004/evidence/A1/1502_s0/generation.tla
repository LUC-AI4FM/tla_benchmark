---------------------------- MODULE spec ----------------------------

CONSTANT Op(_)

VARIABLE x

Init == x = 0

Next == x' \in Op(x)

Forty2 == {y \in {42} : TRUE}

SubsetHelper == SUBSET {1, 2}

=============================================================================