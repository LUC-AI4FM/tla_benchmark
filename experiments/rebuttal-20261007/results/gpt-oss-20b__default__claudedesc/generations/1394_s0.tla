MODULE x_unchanged
EXTENDS Naturals

VARIABLES x, y, z

Init == /\ x \in {1,2,3}
        /\ y \in {1,2,3}
        /\ z \in {1,2,3}

Next == /\ y' = y + 1
        /\ UNCHANGED <<x, z>>

vars == <<x, y, z>>

Spec == Init /\ [][Next]_vars


MODULE Github702
EXTENDS Naturals

\* Constant-valued operator fizzbuzz
\* operator fizzbuzz == 1

INSTANCE x_unchanged WITH x = fizzbuzz

Spec == INSTANCE x_unchanged.Spec