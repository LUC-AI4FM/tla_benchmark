---------------------------- MODULE test201b ----------------------------
\* Test of INSTANCE inside a LET context.
\* This module is the instantiated module. It has a single state variable x
\* and one defined operator, xplus1. The Init, Next and Spec definitions are
\* minimal additions that let the module be used on its own. They do not add
\* any behavior beyond what the description states.

EXTENDS Naturals

VARIABLES x

vars == << x >>

xplus1 == x + 1

\* Minimal initial condition. The original module puts no constraint on x.
Init == x \in Nat

\* No actions are described, so every step leaves the state unchanged.
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================