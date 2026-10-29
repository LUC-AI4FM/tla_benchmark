---- MODULE ToggleXY ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

TypeOK == x \in Nat /\ y \in Nat

Init == x = 0 /\ y = 0

Next == x' = 1 - x /\ y' = y

\* ENABLED predicates over explicit actions
EnabledNext == ENABLED Next

EnabledToggle == ENABLED (x' = 1 - x /\ UNCHANGED y)

\* Safety-style specification
SafetySpec == Init /\ [][Next]_<<x, y>>

\* Liveness-style specification strengthening the safety specification
LiveSpec == SafetySpec /\ WF_<<x, y>>(Next)

Spec == LiveSpec

\* Invariants
XInRange == x \in {0, 1}
YZero == y = 0

\* Liveness properties
XEventuallyOne == <>(x = 1)
XInfinitelyToggles == []<>(x = 1) /\ []<>(x = 0)
====