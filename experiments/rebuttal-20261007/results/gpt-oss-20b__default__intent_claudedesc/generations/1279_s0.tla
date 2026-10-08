MODULE NextStateConstraintDemo
EXTENDS Naturals

VARIABLE x

Init ==
    x = 23

Next ==
    \/ x' = x
    \/ ∃ v ∈ {0,1} : (v > 0) /\ x' = v

Spec == Init /\ [][Next]_x

SafetyInvariant == x # 0