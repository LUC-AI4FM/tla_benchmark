---------------------------- MODULE EnabledTest ----------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = 0
        /\ y = 0

Next == /\ x' = 1 - x
        /\ y' = y

SafeSpec == Init /\ [][Next]_vars

LiveSpec == SafeSpec /\ WF_vars(Next)

\* Enablement of a transition that only constrains primed variables.
\* Any state can move to x' = 1, y' = 0, so this is always TRUE.
NoPre == /\ x' = 1
         /\ y' = 0

\* The same transition with an added current-state precondition.
\* It is enabled only in states where x = 0.
WithPre == /\ x = 0
           /\ x' = 1
           /\ y' = 0

F == ENABLED NoPre

G == (ENABLED WithPre) => (ENABLED NoPre)

=============================================================================