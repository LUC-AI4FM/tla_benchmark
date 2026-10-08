---------------------------- MODULE spec ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Op(_)

VARIABLE x

Init == x = 0

Next == x' \in Op(x)

Forty2(arg) == SUBSET {1, 2, 3}

=============================================================================