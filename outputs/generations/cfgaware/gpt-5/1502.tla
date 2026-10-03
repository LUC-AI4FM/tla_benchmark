--------------------------- MODULE TinyMachine ---------------------------
CONSTANT Op

VARIABLE x

Init == x = 0

Next == x' \in Op(x)

Forty2 == SUBSET {42}

IsForty2SubsetOf(S) == Forty2 \subseteq S
============================================================================