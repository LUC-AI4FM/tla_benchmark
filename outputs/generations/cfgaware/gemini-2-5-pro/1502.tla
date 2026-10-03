---- MODULE SimpleStateMachine ----
EXTENDS Integers

CONSTANT Op(_)

VARIABLE x

Init == x = 0

Next == x' \in Op(x)

Forty2(S) == {y \in S : y = 42}

================================