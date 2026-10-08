------------------------------ MODULE SimpleState ------------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

Init == \E v \in {0,1} : (x = v /\ v < 1)

Stutter == x' = x

Next == Stutter

Spec == Init /\ [][Next]_vars

Inv == x < 1

StableEventually == <> [] (x' = x)

CHECK Inv WITH INVARIANT Inv
CHECK StableEventually WITH LIVENESS StableEventually
=============================================================================