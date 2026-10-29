---------------------------- MODULE OpConstant ----------------------------
EXTENDS Naturals

CONSTANT Op(_)

VARIABLE x

Init == x = 0

Next == x' \in Op(x)

Forty2(n) == {n, 42}

Forty2Subsets(n) == SUBSET Forty2(n)

=============================================================================