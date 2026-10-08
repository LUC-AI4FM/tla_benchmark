MODULE SimpleState
EXTENDS Naturals

VARIABLE x

AllowedSet == {1, 2, 3}

Init == x = 1

Stutter == x' = x

Assign(v) == /\ v \in AllowedSet
            /\ v > 0
            /\ x' = v

Next == Stutter \/ ∃v ∈ AllowedSet : Assign(v)

SafetyInvariant == [] (x != 0)

TransitionConstraint == [] (x' = x \/ (x' ∈ AllowedSet /\ x'>0))

Spec == Init /\ [][Next]_x