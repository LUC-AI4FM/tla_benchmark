----------------------------- MODULE TrivialStuttering -----------------------------

EXTENDS Integers

CONSTANTS Zero
ASSUME Zero = 0

VARIABLES x, y

vars == <<x, y>>

Init == x = Zero /\ y = Zero /\ x = y

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================