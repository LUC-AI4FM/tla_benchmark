---------------------------- MODULE ToggleXY ----------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in Nat
          /\ y \in Nat

Init == /\ x = 0
        /\ y = 0

Next == /\ x' = 1 - x
        /\ y' = y

\* ENABLED predicate over the named next-state action
EnabledNext == ENABLED Next

\* ENABLED predicate over an explicitly written action
EnabledExplicit == ENABLED (x' = 1 - x /\ y' = y)

\* Safety invariants
XInRange == x \in {0, 1}
YUnchanged == y = 0

\* Safety-style specification
SafetySpec == Init /\ [][Next]_vars

\* Liveness-style specification strengthened with weak fairness
LiveSpec == SafetySpec /\ WF_vars(Next)

Spec == LiveSpec

\* Liveness properties
XEventuallyOne == <>(x = 1)
XToggles == []<>(x = 1) /\ []<>(x = 0)

=============================================================================