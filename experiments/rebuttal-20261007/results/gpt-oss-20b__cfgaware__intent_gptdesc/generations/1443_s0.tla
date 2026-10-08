------------------------------ MODULE Counter ------------------------------
IMPORTS Integers

VARIABLE state

Init == state = 0

Next == state' = (state + 1) MOD 3

Spec == Init /\ []Next

Safety          == [] (state ∈ {0, 1, 2})
Determinism     == [] (state' = (state + 1) MOD 3)
Reachable1      == <> (state = 1)
Reachable2      == <> (state = 2)
WrapAround      == <> (state = 2 /\ state' = 0)
CycleLiveness   == []<>(state = 0) /\ []<>(state = 1) /\ []<>(state = 2)

THEOREM SafetyThm:          Spec => Safety
THEOREM DeterminismThm:     Spec => Determinism
THEOREM Reachable1Thm:      Spec => Reachable1
THEOREM Reachable2Thm:      Spec => Reachable2
THEOREM WrapAroundThm:      Spec => WrapAround
THEOREM CycleLivenessThm:   Spec => CycleLiveness

=============================================================================