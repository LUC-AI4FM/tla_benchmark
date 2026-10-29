---------------------------- MODULE test47a ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

\* The described module provides no initialization; x is left unconstrained.
Init == TRUE

\* The described module provides no transitions; the only steps are stuttering steps.
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================