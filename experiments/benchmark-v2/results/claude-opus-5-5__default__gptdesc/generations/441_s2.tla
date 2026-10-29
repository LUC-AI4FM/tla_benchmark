---- MODULE ToggleXY ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in Nat
          /\ y \in Nat

Init == /\ x = 0
        /\ y = 0

Next == /\ x' = 1 - x
        /\ y' = y

\* ENABLED predicates over explicit actions
EnabledNext == ENABLED Next

EnabledToggle == ENABLED (/\ x' = 1 - x /\ y' = y)

\* Safety-style specification
SafetySpec == Init /\ [][Next]_<<x, y>>

\* Liveness-style specification strengthening safety with weak fairness
LiveSpec == SafetySpec /\ WF_<<x, y>>(Next)

Spec == LiveSpec

\* Safety invariants
XInRange == x \in {0, 1}
YConstant == y = 0

\* Liveness properties
XEventuallyOne == []<>(x = 1)
XEventuallyZero == []<>(x = 0)

====