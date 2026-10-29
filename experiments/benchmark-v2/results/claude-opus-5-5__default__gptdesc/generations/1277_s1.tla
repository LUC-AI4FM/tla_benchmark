---------------------------- MODULE TemporalSubscriptExample ----------------------------
EXTENDS Naturals

VARIABLES s

vars == <<s>>

\* Parameterized action operator: chooses a value in 0..1 such that the
\* argument equals that value and is strictly positive.
Next(var) == \E val \in 0..1 : var = val /\ var > 0

Init == s = ""

\* The overall specification: initialize s to the empty string and constrain
\* every step with the boxed action formula [Next(s')]_s.
Spec == Init /\ [][Next(s')]_s

=============================================================================