---- MODULE ToggleXY ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Init == x = 0 /\ y = 0

Next == x' = 1 - x /\ y' = y

TypeOK == x \in {0, 1} /\ y \in Nat

\* ENABLED predicates over explicit actions
EnabledNext == ENABLED Next

EnabledStutterNext == ENABLED [Next]_vars

\* Safety-style specification
SafetySpec == Init /\ [][Next]_vars

\* Liveness-style specification: safety strengthened with weak fairness
LiveSpec == SafetySpec /\ WF_vars(Next)

Spec == LiveSpec

\* Safety invariants
TypeInvariant == TypeOK
YConstant == y = 0

\* Liveness properties
XEventuallyOne == <>(x = 1)
XToggles == []<>(x = 1) /\ []<>(x = 0)

THEOREM SafetySpec => []TypeOK
THEOREM LiveSpec => XToggles
====